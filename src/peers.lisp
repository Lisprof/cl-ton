;;;; cl-ton -- a TON blockchain client for Common Lisp.
;;;;
;;;; Copyright (c) 2026 lisprof
;;;;
;;;; Licensed under the Apache License, Version 2.0 (the "License");
;;;; you may not use this file except in compliance with the License.
;;;; You may obtain a copy of the License at
;;;;
;;;;     https://www.apache.org/licenses/LICENSE-2.0
;;;;
;;;; Unless required by applicable law or agreed to in writing, software
;;;; distributed under the License is distributed on an "AS IS" BASIS,
;;;; WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;;;; See the License for the specific language governing permissions and
;;;; limitations under the License.

;;;; peers.lisp -- evaluating liteserver candidates found through the DHT, and the diagnose report.
;;;;
;;;; A candidate is probed with liteServer queries over ADNL UDP (a liteServer.query wrapper around liteServer.getTime and
;;;; liteServer.getMasterchainInfo, as a lite client over TCP sends them).  Whether a node answers lite queries over UDP at all is
;;;; the question the DIAGNOSE report answers on a real network.  A probe's answer is NOT trusted for anything but ranking: the
;;;; head and every state still come from the verifying lite client.
;;;;
;;;; Score (lower is better): ALPHA * round trip seconds + BETA * blocks behind the best head seen + GAMMA * failure rate.  With the
;;;; defaults one block behind costs as much as a second of round trip, so freshness decides between nodes whose round trips are
;;;; within a block or two of each other and a slow but fresh node does not lose to a fast stale one.

(in-package :cl-ton)

(defstruct (lite-candidate (:copier nil))
  host port public
  (rtt nil) (seqno nil) (utime nil)
  (probes 0) (failures 0))

(defun lite-candidate-failure-rate (c)
  (if (zerop (lite-candidate-probes c)) 0 (/ (lite-candidate-failures c) (lite-candidate-probes c))))

(defun lite-candidate-score (c max-seqno &key (alpha 1.0) (beta 1.0) (gamma 5.0) (unknown-rtt 10.0) (unknown-lag 30))
  "The score of candidate C (lower is better), MAX-SEQNO being the best head any candidate reported."
  (+ (* alpha (or (lite-candidate-rtt c) unknown-rtt))
     (* beta (if (lite-candidate-seqno c) (max 0 (- max-seqno (lite-candidate-seqno c))) unknown-lag))
     (* gamma (lite-candidate-failure-rate c))))

(defun rank-candidates (candidates &rest weights)
  "CANDIDATES best first by LITE-CANDIDATE-SCORE (WEIGHTS: :alpha :beta :gamma)."
  (let ((max-seqno (reduce #'max (mapcar (lambda (c) (or (lite-candidate-seqno c) 0)) candidates) :initial-value 0)))
    (mapcar #'cdr (sort (mapcar (lambda (c) (cons (apply #'lite-candidate-score c max-seqno weights) c)) candidates)
                        #'< :key #'car))))

(defun select-pools (ranked &key (hot 4))
  "(VALUES HOT WARM): the HOT best candidates that answer (a seqno is known), and the rest that answered at least once."
  (let ((answering (remove-if-not #'lite-candidate-rtt ranked)))
    (values (subseq answering 0 (min hot (length answering)))
            (nthcdr (min hot (length answering)) answering))))

(defun lite-candidate-record (c probe)
  "Fold the result of a LITE-UDP-PROBE into candidate C: smoothed round trip, newest head, failure count."
  (incf (lite-candidate-probes c))
  (if (getf probe :lite)
      (setf (lite-candidate-rtt c) (let ((rtt (getf probe :rtt)))
                                     (if (lite-candidate-rtt c) (+ (* 0.7 (lite-candidate-rtt c)) (* 0.3 rtt)) rtt))
            (lite-candidate-seqno c) (or (getf probe :seqno) (lite-candidate-seqno c))
            (lite-candidate-utime c) (or (getf probe :now) (lite-candidate-utime c)))
      (incf (lite-candidate-failures c)))
  c)

;;; --- the probe -----------------------------------------------------------------------------------------------------------------------

(defun %lite-udp-ask (adnl host port public function timeout)
  "The decoded answer to the lite API FUNCTION (a TL object), wrapped in liteServer.query, or a condition."
  (let ((query (tl-encode (tl-make "liteServer.query" :data (coerce (tl-encode function) 'tl-octets)))))
    (tl-decode (adnl-udp-query adnl host port public query :timeout timeout))))

(defun %lite-probe (ask)
  "The lite check shared by the UDP and the TCP probe: ASK, a function of a lite API request (a TL object) returning the decoded
answer, is used for liteServer.getTime and liteServer.getMasterchainInfo.  A plist: :LITE true when the node answered as a liteserver,
:RTT seconds of the getTime round trip, :NOW its clock, :SEQNO its head, :ERROR what went wrong."
  (let* ((start (get-internal-real-time))
         (time (funcall ask (tl-make "liteServer.getTime")))
         (rtt (/ (- (get-internal-real-time) start) internal-time-units-per-second)))
    (cond
      ((tl-is time "liteServer.error")
       (list :lite nil :error (format nil "liteServer.error ~D ~A" (tl-get time :code) (let ((m (tl-get time :message))) (if (stringp m) m (sb-ext:octets-to-string (as-octets m) :external-format :latin-1))))))
      ((not (tl-is time "liteServer.currentTime"))
       (list :lite nil :error (format nil "unexpected ~A" (tl-obj-name time))))
      (t (let ((info (ignore-errors (funcall ask (tl-make "liteServer.getMasterchainInfo")))))
           (list :lite t :rtt rtt :now (tl-get time :now)
                 :seqno (and info (tl-is info "liteServer.masterchainInfo") (tl-get (tl-get info :last) :seqno))))))))

(defun lite-udp-probe (adnl host port public &key (timeout 3))
  "Ask the node at HOST:PORT (key PUBLIC) liteServer.getTime and liteServer.getMasterchainInfo over ADNL UDP; the plist of %LITE-PROBE."
  (handler-case (%lite-probe (lambda (function) (%lite-udp-ask adnl host port public function timeout)))
    (adnl-udp-timeout () (list :lite nil :error "no answer"))
    (error (e) (list :lite nil :error (princ-to-string e)))))

(defun %lite-tcp-ask (conn function timeout)
  "The decoded answer to the lite API FUNCTION (a TL object) asked on the ADNL ext connection CONN, or a condition."
  (let* ((id (tl-random-int256))
         (query (tl-encode (tl-make "liteServer.query" :data (coerce (tl-encode function) 'tl-octets))))
         (deadline (+ (get-internal-real-time) (round (* timeout internal-time-units-per-second)))))
    (adnl-send-packet conn (tl-encode (tl-make "adnl.message.query" :query-id id :query query)))
    (loop
      (let* ((left (/ (- deadline (get-internal-real-time)) internal-time-units-per-second))
             (packet (if (plusp left) (adnl-recv-packet conn :timeout left) :timeout)))
        (when (eq packet :timeout)
          (error 'adnl-timeout :format-control "no answer within ~As" :format-arguments (list timeout)))
        (let ((message (ignore-errors (tl-decode packet))))
          (when (and message (tl-is message "adnl.message.answer")
                     (equalp (as-octets (tl-get message :query-id)) (as-octets id)))
            (return (tl-decode (as-octets (tl-get message :answer))))))))))

(defun lite-tcp-probe (host port public &key (timeout 3))
  "Ask the node at HOST:PORT (ADNL ext TCP, the server key PUBLIC) liteServer.getTime and liteServer.getMasterchainInfo; the plist of
%LITE-PROBE.  A port that accepts the connection but never acknowledges the handshake is not an ADNL server of that key."
  (let ((conn nil))
    (unwind-protect
         (handler-case
             (progn
               (setf conn (adnl-connect host port public :timeout timeout))
               (when (eq :timeout (adnl-recv-packet conn :timeout timeout))
                 (return-from lite-tcp-probe
                   (list :lite nil :error "TCP open, no handshake ack (not an ADNL server of this key)")))
               (%lite-probe (lambda (function) (%lite-tcp-ask conn function timeout))))
           (adnl-timeout () (list :lite nil :error "no answer"))
           (error (e) (list :lite nil :error (princ-to-string e))))
      (when conn (ignore-errors (adnl-conn-close conn))))))

;;; --- the TCP port scan ---------------------------------------------------------------------------------------------------------------

(defun %tcp-open-p (host port timeout)
  (let ((socket (ignore-errors (adnl-tcp-connect host port :timeout timeout))))
    (when socket (ignore-errors (sb-bsd-sockets:socket-close socket)) t)))

(defun tcp-scan (hosts from to &key (timeout 1.5) (width 256) progress)
  "The (HOST . PORT) pairs, sorted, that accept a TCP connection: every port FROM..TO of every host in HOSTS, WIDTH connections at a
time.  The ports are the outer loop, so a host sees one connection per sweep of all the hosts.  PROGRESS, when given, is called with
the percent done about every 5 percent."
  (let* ((hosts (coerce hosts 'vector)) (count (length hosts)) (total (* count (max 0 (1+ (- to from)))))
         (next 0) (found '()) (lock (sb-thread:make-mutex)) (step (max 1 (floor total 20))))
    (when (plusp total)
      (flet ((worker ()
               (loop (let ((i (sb-thread:with-mutex (lock) (prog1 next (incf next)))))
                       (when (>= i total) (return))
                       (when (and progress (zerop (mod i step))) (ignore-errors (funcall progress (floor (* 100 i) total))))
                       (let ((host (aref hosts (mod i count))) (port (+ from (floor i count))))
                         (when (%tcp-open-p host port timeout)
                           (sb-thread:with-mutex (lock) (push (cons host port) found))))))))
        (mapc #'sb-thread:join-thread
              (loop repeat (min width total) collect (sb-thread:make-thread #'worker :name "tcp-scan")))))
    (sort found (lambda (a b) (or (string< (car a) (car b)) (and (string= (car a) (car b)) (< (cdr a) (cdr b))))))))

;;; --- the diagnose --------------------------------------------------------------------------------------------------------------------

(defun %parallel-map (function list &optional (width 8))
  "FUNCTION over LIST on up to WIDTH threads at a time; the results in order."
  (let ((results (make-array (length list) :initial-element nil))
        (items (coerce list 'vector))
        (next 0)
        (lock (sb-thread:make-mutex)))
    (flet ((worker ()
             (loop (let ((i (sb-thread:with-mutex (lock) (prog1 next (incf next)))))
                     (when (>= i (length items)) (return))
                     (setf (aref results i) (handler-case (funcall function (aref items i)) (error () nil)))))))
      (mapc #'sb-thread:join-thread
            (loop repeat (min width (length items)) collect (sb-thread:make-thread #'worker :name "probe"))))
    (coerce results 'list)))

(defun %config-liteservers (path)
  "The (HOST PORT PUBLIC) of every liteserver of the global config at PATH (its TCP address and its key)."
  (let ((config (json-decode (read-global-config path))))
    (loop for entry across (coerce (json-get config "liteservers") 'vector)
          collect (let ((ip (ldb (byte 32 0) (json-get entry "ip"))))
                    (list (format nil "~D.~D.~D.~D" (ldb (byte 8 24) ip) (ldb (byte 8 16) ip) (ldb (byte 8 8) ip) (ldb (byte 8 0) ip))
                          (json-get entry "port")
                          (base64-decode (json-get (json-get entry "id") "key")))))))

(defun dht-diagnose (&key (stream *standard-output*) report-file config-path cache-file bootstrap
                          (rounds 8) (config-probes 10) (timeout 3) (dht-timeout 2.0)
                          (scan-from 1) (scan-to 65535) (scan-timeout 1.5) (scan-width 256) (keys-per-port 8))
  "Crawl the DHT from the bootstrap nodes; scan the TCP ports SCAN-FROM..SCAN-TO of the hosts of the DHT nodes that answered, and
on every open port ask liteServer.getTime / getMasterchainInfo over ADNL ext TCP with each key those nodes use on that host (the
DHT publishes the UDP address and the ADNL key only, not the lite TCP port or key); with CONFIG-PATH also look the liteservers of that
global config up in the DHT; print a report to STREAM (and REPORT-FILE).  Returns a plist with the counts: :DHT-NODES, :TCP-HOSTS
(scanned), :TCP-OPEN (open ports), :TCP-LITE (answering as liteservers), :CONFIG-FOUND (config liteservers with a DHT address),
:CONFIG-LITE (of those, answering over UDP)."
  (let* ((file (and report-file (open report-file :direction :output :if-exists :supersede :external-format :utf-8)))
         (out (if file (make-broadcast-stream stream file) stream))
         (dht (dht-start :bootstrap (or bootstrap *dht-bootstrap*) :timeout dht-timeout :cache-file cache-file))
         (adnl (dht-adnl dht))
         (summary (list :dht-nodes 0 :tcp-hosts 0 :tcp-open 0 :tcp-lite 0 :config-found 0 :config-lite 0)))
    (unwind-protect
         (progn
           (format out "== ADNL/DHT diagnose ==~%bootstrap nodes: ~D~%" (dht-peer-count dht))
           (let ((answering (count-if #'identity (%parallel-map (lambda (p) (dht-ping dht p)) (loop for p being the hash-values of (dht-peers dht) collect p)))))
             (format out "bootstrap nodes answering dht.ping over ADNL UDP: ~D~%" answering)
             (when (and (zerop answering) (dht-last-error dht))
               (format out "local error while sending: ~A~%" (dht-last-error dht))))
           (dotimes (round rounds)
             (dht-find-nodes dht (ironclad:random-data 32))
             (format out "crawl round ~D: ~D DHT nodes known~%" (1+ round) (dht-peer-count dht)))
           (setf (getf summary :dht-nodes) (dht-peer-count dht))
           (when cache-file (dht-save-cache dht cache-file))
           ;; the hosts of the DHT nodes that answered: TCP port scan, then the lite probe on every open port
           (let* ((answering (loop for p being the hash-values of (dht-peers dht) when (plusp (dht-peer-answers p)) collect p))
                  (hosts (sort (remove-duplicates (mapcar #'dht-peer-host answering) :test #'string=) #'string<))
                  (keys (make-hash-table :test 'equal)))
             (dolist (p answering) (pushnew (dht-peer-public p) (gethash (dht-peer-host p) keys) :test #'equalp))
             (format out "~%-- TCP scan of ~D hosts of DHT nodes that answered, ports ~D-~D, ~D at a time --~%"
                     (length hosts) scan-from scan-to scan-width)
             (finish-output out)
             (let ((open (tcp-scan hosts scan-from scan-to :timeout scan-timeout :width scan-width
                                   :progress (lambda (percent) (format out "scan ~D%~%" percent) (finish-output out)))))
               (setf (getf summary :tcp-hosts) (length hosts) (getf summary :tcp-open) (length open))
               (format out "~D open TCP ports; liteServer.getTime / getMasterchainInfo over ADNL ext TCP with the node keys of the host:~%"
                       (length open))
               (dolist (pair open)
                 (let ((publics (subseq (gethash (car pair) keys) 0 (min keys-per-port (length (gethash (car pair) keys))))))
                   (let ((results (%parallel-map (lambda (public) (lite-tcp-probe (car pair) (cdr pair) public :timeout timeout)) publics 4)))
                     (loop for public in publics for r in results
                           do (when (getf r :lite) (incf (getf summary :tcp-lite)))
                              (format out "~A:~D open, key ~A: ~A~%" (car pair) (cdr pair) (subseq (octets->hex (adnl-short-id public)) 0 12)
                                      (if (getf r :lite)
                                          (format nil "LITE OK over TCP  rtt ~,0Fms  seqno ~A" (* 1000 (getf r :rtt)) (getf r :seqno))
                                          (format nil "no lite (~A)" (getf r :error))))))))))
           ;; the liteservers of the config, looked up in the DHT
           (when config-path
             (let ((entries (subseq (%config-liteservers config-path) 0 (min config-probes (length (%config-liteservers config-path))))))
               (format out "~%-- ~D liteservers of ~A: DHT address record and UDP probe --~%" (length entries) config-path)
               (dolist (e entries)
                 (destructuring-bind (host port public) e
                   (let* ((short (adnl-short-id public))
                          (list (dht-find-address dht short)))
                     (format out "~A:~D (tcp in config) id ~A: " host port (subseq (octets->hex short) 0 12))
                     (if (null list)
                         (format out "no address record in the DHT~%")
                         (multiple-value-bind (uhost uport) (%dht-udp-address list)
                           (incf (getf summary :config-found))
                           (let ((r (and uhost (lite-udp-probe adnl uhost uport public :timeout timeout))))
                             (format out "DHT says udp ~A:~D; ~A~%" uhost uport
                                     (if (and r (getf r :lite))
                                         (progn (incf (getf summary :config-lite))
                                                (format nil "LITE OK over UDP, rtt ~,0Fms seqno ~A" (* 1000 (getf r :rtt)) (getf r :seqno)))
                                         (format nil "no lite over UDP (~A)" (and r (getf r :error)))))))))))))
           (format out "~%== summary: ~D DHT nodes; ~D hosts scanned, ~D open TCP ports, ~D answer liteServer queries over TCP; config liteservers with a DHT address ~D, answering over UDP ~D ==~%"
                   (getf summary :dht-nodes) (getf summary :tcp-hosts) (getf summary :tcp-open) (getf summary :tcp-lite)
                   (getf summary :config-found) (getf summary :config-lite))
           summary)
      (dht-stop dht)
      (when file (close file)))))

;;; --- the upstream pool -----------------------------------------------------------------------------------------------------------------
;;;
;;; The transport of a lite client that talks to SEVERAL liteservers itself: the logic of the native proxy, moved in (the proxy is
;;; deleted at the end of Stage L).  A query goes to the best upstream; when that one has not answered after an adaptive HEDGE DELAY a
;;; second is asked as well and the first valid answer wins; an attempt that fails outright (connection lost, "not ready", or, for a
;;; block or history query, any error answer) starts the next at once; at most *POOL-MAX-ATTEMPTS* upstreams are used and never past
;;; the query's time budget.  An upstream that timed out or died is avoided for a time that doubles with every repeat, one that
;;; answered "not ready" for a while, one whose answer the client reported as not verifying (UPSTREAM-POOL-APPLY-VERDICT) for a ban
;;; that doubles with every repeat.  Upstreams are chosen at random weighted by speed and failures, and upstreams far behind the best
;;; head known are avoided.  Entries with a slice (a server that serves only part of the shards) are not used.
;;;
;;; The pool takes the place of the ADNL-EXT-CLIENT in a LITE-CLIENT (see OPEN-LITE-CLIENT-POOL): UPSTREAM-POOL-SEND-QUERY is
;;; ADNL-EXT-CLIENT-SEND-QUERY for the whole set and signals the same conditions (ADNL-TIMEOUT, ADNL-CLOSED, ADNL-NOT-READY); a
;;; liteServer.error answer is returned as the octets the upstream sent.

(defparameter *pool-max-active* 8
  "How many upstream sessions are open at once; the others of a long list stand by and are opened when no active one is alive.")
(defparameter *pool-max-attempts* 4 "At most this many upstreams are tried for one query.")
(defparameter *pool-hedge-delay* 2
  "Seconds a query waits for its first upstream before a second one is asked as well, until enough answers have been measured to
adapt (see %POOL-HEDGE-DELAY).  The first attempt is not cancelled: whichever valid answer arrives first wins.")
(defparameter *pool-hedge-min* 0.5 "Lower bound of the adaptive hedge delay.")
(defparameter *pool-hedge-max* 4.0 "Upper bound of the adaptive hedge delay.")
(defparameter *pool-lagging-penalty* 30 "Seconds an upstream that answered \"not ready\" is avoided while others are left.")
(defparameter *pool-max-lag* 10
  "How many masterchain blocks behind the best head known an upstream may be and still be chosen.")
(defparameter *pool-failure-penalty* 10
  "Seconds an upstream that timed out or lost its connection is avoided; doubles with every consecutive failure up to
*POOL-FAILURE-PENALTY-MAX*, and an answer clears it.")
(defparameter *pool-failure-penalty-max* 120)
(defparameter *pool-rejection-ban* 120
  "Seconds an upstream is avoided after the client reported an answer of it that did not verify; doubled by each further report
within an hour of the ban ending, at most *POOL-REJECTION-BAN-MAX*.")
(defparameter *pool-rejection-ban-max* 3600)
(defparameter *pool-answer-memory* 512 "How many of the latest answers the pool remembers the upstream of, to match a verdict to it.")
(defparameter *pool-startup-grace* 3 "Seconds a query waits for an upstream to come alive when none is.")

(defstruct (pool-upstream (:copier nil))
  name client host port public
  (seqno 0)                             ; the newest masterchain seqno seen in one of its answers
  (penalty-until 0)                     ; internal real time until which it is avoided (failure, "not ready")
  (ban-until 0)                         ; ... until which it is avoided because an answer of it did not verify
  (reject-streak 0) (fail-streak 0)
  (slowness nil)                        ; moving average of its answer time relative to the method's usual time (1.0 = typical)
  (started-p t))                        ; NIL on standby: its session has not been opened yet

(defstruct (upstream-pool (:constructor %make-upstream-pool) (:copier nil))
  upstreams (max-active *pool-max-active*) (max-seqno 0) (stopped nil)
  (method-latency (make-hash-table :test 'equal)) ; method -> (n . moving average of seconds)
  (answer-origins (make-hash-table :test 'equal)) ; hex SHA-256 of an answer -> the upstream that gave it
  (answer-order '())                    ; the keys of ANSWER-ORIGINS, newest first
  (lock (sb-thread:make-mutex :name "upstream pool")))

(defun open-upstream-pool (entries &key (max-active *pool-max-active*) log)
  "A pool over the liteservers ENTRIES, a list of (HOST PORT PUBLIC) with PUBLIC the server's 32 key octets.  MAX-ACTIVE sessions are
opened at once, in random order so the load spreads over the public servers; the others stand by.  LOG, a function of (control &rest
args), receives one line per session event."
  (let* ((max-active (max 1 max-active)) (pool (%make-upstream-pool :max-active max-active)))
    (setf (upstream-pool-upstreams pool)
          (loop for (host port public) in (%shuffle entries)
                for i from 0
                for active = (< i max-active)
                collect (make-pool-upstream :name (format nil "~A:~D" host port) :host host :port port :public public
                                            :started-p active
                                            :client (open-adnl-ext-client host port public :log log :start active))))
    pool))

(defun open-upstream-pool-from-config (global-config &rest keys &key max-active log)
  "OPEN-UPSTREAM-POOL over the liteservers of the global config file GLOBAL-CONFIG (a path); servers with a slice are left out."
  (declare (ignore max-active log))
  (apply #'open-upstream-pool
         (loop for (host port public slices) in (%global-config-liteservers (json-decode (read-global-config global-config)))
               unless slices collect (list host port public))
         keys))

(defun close-upstream-pool (pool)
  (setf (upstream-pool-stopped pool) t)
  (dolist (up (upstream-pool-upstreams pool)) (close-adnl-ext-client (pool-upstream-client up))))

(defun upstream-pool-alive-p (pool)
  (and (not (upstream-pool-stopped pool))
       (some (lambda (up) (adnl-ext-client-alive-p (pool-upstream-client up))) (upstream-pool-upstreams pool))))

;;; selection

(defun %pool-alive-upstreams (pool exclude)
  (loop for up in (upstream-pool-upstreams pool)
        when (and (not (member up exclude)) (adnl-ext-client-alive-p (pool-upstream-client up))) collect up))

(defun %pool-penalized-p (up)
  (let ((now (get-internal-real-time)))
    (or (> (pool-upstream-penalty-until up) now) (> (pool-upstream-ban-until up) now))))

(defun %pool-weight (up)
  "How much UP is preferred among otherwise equal candidates; never zero, so a recovered upstream is noticed."
  (/ 1.0 (* (expt (max 0.25 (min 4.0 (or (pool-upstream-slowness up) 1.0))) 2) (1+ (pool-upstream-fail-streak up)))))

(defun %pool-pick (candidates)
  (let* ((weights (mapcar #'%pool-weight candidates)) (r (random (reduce #'+ weights))))
    (loop for up in candidates for w in weights
          do (decf r w) (when (<= r 0) (return up))
          finally (return (car (last candidates))))))

(defun %pool-select (pool wait-seqno exclude)
  "A random alive upstream not in EXCLUDE, or NIL: those that recently failed, answered \"not ready\" or were banned only when no
other is left; those more than *POOL-MAX-LAG* blocks behind the best known head avoided; with WAIT-SEQNO the upstreams known to be at
or past it preferred, else the most advanced ones, so a stale upstream is never the one made to wait."
  (let* ((candidates (%pool-alive-upstreams pool exclude))
         (healthy (remove-if #'%pool-penalized-p candidates))
         (best (sb-thread:with-mutex ((upstream-pool-lock pool)) (upstream-pool-max-seqno pool)))
         (base (or healthy candidates))
         (base (if (zerop best)
                   base
                   (or (remove-if (lambda (up) (< (pool-upstream-seqno up) (- best *pool-max-lag*))) base) base)))
         (ahead (and wait-seqno (remove-if-not (lambda (up) (>= (pool-upstream-seqno up) wait-seqno)) base)))
         (chosen (or ahead
                     (and wait-seqno base
                          (let ((top (reduce #'max base :key #'pool-upstream-seqno)))
                            (remove-if-not (lambda (up) (= (pool-upstream-seqno up) top)) base)))
                     base)))
    (and chosen (%pool-pick chosen))))

(defun %pool-activate-standby (pool n)
  "Open the session of up to N upstreams on standby; how many were started."
  (let ((started 0))
    (dolist (up (upstream-pool-upstreams pool) started)
      (when (>= started n) (return started))
      (unless (pool-upstream-started-p up)
        (setf (pool-upstream-started-p up) t)
        (start-adnl-ext-client (pool-upstream-client up))
        (incf started)))))

;;; what the answers teach

(defun %pool-note-seqno (pool up seqno)
  (when (integerp seqno)
    (sb-thread:with-mutex ((upstream-pool-lock pool))
      (setf (pool-upstream-seqno up) (max (pool-upstream-seqno up) seqno)
            (upstream-pool-max-seqno pool) (max (upstream-pool-max-seqno pool) seqno)))))

(defun %pool-learn (pool up answer)
  "Update UP's head from a masterchainInfo, masterchainInfoExt, accountState or runMethodResult ANSWER (octets); returns ANSWER."
  (let ((obj (handler-case (tl-decode answer) (error () nil))))
    (when (tl-obj-p obj)
      (cond ((or (tl-is obj "liteServer.masterchainInfo") (tl-is obj "liteServer.masterchainInfoExt"))
             (let ((last (tl-get obj :last)))
               (when (tl-obj-p last) (%pool-note-seqno pool up (tl-get last :seqno)))))
            ((or (tl-is obj "liteServer.accountState") (tl-is obj "liteServer.runMethodResult"))
             (let ((id (tl-get obj :id)))
               (when (and (tl-obj-p id) (eql (tl-get id :workchain) -1))
                 (%pool-note-seqno pool up (tl-get id :seqno))))))))
  answer)

(defun %pool-wait-prefix (up wait-seqno wait-timeout-ms elapsed-ms)
  "The octets (possibly none) of the waitMasterchainSeqno prefix to send UP: dropped when UP is known to be at or past the seqno (it
answers at once), else forwarded with what is left of the timeout, so the upstream really waits for the block."
  (if (>= (pool-upstream-seqno up) wait-seqno)
      (make-array 0 :element-type '(unsigned-byte 8))
      (tl-encode (tl-make "liteServer.waitMasterchainSeqno" :seqno wait-seqno :timeout-ms (max 0 (- wait-timeout-ms elapsed-ms))))))

(defun %pool-penalize-for (pool up seconds)
  (sb-thread:with-mutex ((upstream-pool-lock pool))
    (setf (pool-upstream-penalty-until up)
          (max (pool-upstream-penalty-until up) (+ (get-internal-real-time) (* seconds internal-time-units-per-second))))))

(defun %pool-note-failure (pool up)
  "UP timed out or lost its connection: avoid it, for longer after each repeat."
  (let ((streak (sb-thread:with-mutex ((upstream-pool-lock pool)) (incf (pool-upstream-fail-streak up)))))
    (%pool-penalize-for pool up (min *pool-failure-penalty-max* (* *pool-failure-penalty* (expt 2 (min 10 (1- streak))))))))

(defun %pool-note-success (pool up method secs)
  "UP answered METHOD in SECS: clear its failure streak and penalty and rate its speed against the usual time of that method."
  (sb-thread:with-mutex ((upstream-pool-lock pool))
    (setf (pool-upstream-fail-streak up) 0 (pool-upstream-penalty-until up) 0)
    (let* ((cell (or (gethash method (upstream-pool-method-latency pool))
                     (setf (gethash method (upstream-pool-method-latency pool)) (cons 0 secs))))
           (usual (max 0.05 (cdr cell)))
           (factor (max 0.25 (min 4.0 (/ secs usual)))))
      (when (>= (car cell) 3)           ; the first few answers define "usual"
        (setf (pool-upstream-slowness up)
              (if (pool-upstream-slowness up) (+ (* 0.7 (pool-upstream-slowness up)) (* 0.3 factor)) factor)))
      (setf (cdr cell) (+ (* 0.8 (cdr cell)) (* 0.2 secs)))
      (incf (car cell)))))

(defun %pool-hedge-delay (pool method wait)
  "Seconds to wait for the first upstream before asking a second as well; NIL for a wait request (those are retried one after the
other, never raced).  Adapts to the measured answer time of METHOD."
  (unless wait
    (let ((cell (sb-thread:with-mutex ((upstream-pool-lock pool)) (gethash method (upstream-pool-method-latency pool)))))
      (if (and cell (>= (car cell) 3))
          (max *pool-hedge-min* (min *pool-hedge-max* (+ 0.3 (* 1.5 (cdr cell)))))
          *pool-hedge-delay*))))

;;; one attempt, and the race

(defun %pool-forward (pool up wait fn-octets started limit)
  "One attempt of a query on UP, at most LIMIT seconds.  (VALUES ANSWER KIND): ANSWER the octets UP sent (NIL when it sent none), KIND
NIL for a good answer, :NOTREADY when UP answered \"not ready\", :ERROR for any other liteServer.error, :TIMEOUT when it stayed
silent, :DEAD when its connection was lost or not up."
  (let* ((elapsed-ms (round (* 1000 (/ (- (get-internal-real-time) started) internal-time-units-per-second))))
         (prefix (if wait
                     (%pool-wait-prefix up (tl-get wait :seqno) (tl-get wait :timeout-ms) elapsed-ms)
                     (make-array 0 :element-type '(unsigned-byte 8))))
         (payload (tl-encode (tl-make "liteServer.query" :data (%cat prefix fn-octets)))))
    (handler-case
        (let ((answer (%pool-learn pool up (adnl-ext-client-send-query (pool-upstream-client up) payload limit))))
          (cond ((proxy-notready-answer-p answer) (values answer :notready))
                ((%answer-detail answer) (values answer :error))
                (t (values answer nil))))
      (adnl-timeout () (values nil :timeout))
      (adnl-closed () (values nil :dead)))))

(defun %pool-attempt (pool up method wait fn-octets started limit)
  "%POOL-FORWARD plus the bookkeeping on UP; runs in its own thread, so a late answer of an attempt that lost the race still teaches
the pool about UP."
  (let ((t0 (get-internal-real-time)))
    (multiple-value-bind (answer kind) (%pool-forward pool up wait fn-octets started limit)
      (case kind
        ((nil) (%pool-note-success pool up method (/ (- (get-internal-real-time) t0) (float internal-time-units-per-second))))
        (:notready (%pool-penalize-for pool up *pool-lagging-penalty*))
        ((:timeout :dead) (%pool-note-failure pool up)))
      (values answer kind))))

(defun %pool-remember-answer (pool answer up)
  "Remember that UP gave ANSWER (octets), so a verdict about it can be applied."
  (let ((key (octets->hex (sha256 answer))))
    (sb-thread:with-mutex ((upstream-pool-lock pool))
      (let ((table (upstream-pool-answer-origins pool)))
        (unless (gethash key table)
          (setf (gethash key table) up)
          (push key (upstream-pool-answer-order pool))
          (when (> (hash-table-count table) *pool-answer-memory*)
            (let ((half (floor *pool-answer-memory* 2)))
              (dolist (old (nthcdr half (upstream-pool-answer-order pool))) (remhash old table))
              (setf (upstream-pool-answer-order pool) (subseq (upstream-pool-answer-order pool) 0 half)))))))))

(defun %pool-race (pool method history wait fn-octets budget started)
  "Answer one query from the upstreams within BUDGET seconds of STARTED: (VALUES ANSWER FAILURE).  ANSWER is the octets of an
upstream's answer (a liteServer.error among them: the last one when every attempt failed); with none, FAILURE says why: :NO-SERVER,
:DEAD or :TIMEOUT.  See the header of this section for the rules."
  (let* ((itu internal-time-units-per-second)
         (deadline (+ started (round (* itu budget))))
         (sem (sb-thread:make-semaphore)) (lock (sb-thread:make-mutex))
         (results '()) (tried '()) (launched 0) (collected 0)
         (last-launch started) (answer nil) (failure :timeout)
         (hedge (%pool-hedge-delay pool method wait))
         (wait-seqno (and wait (tl-get wait :seqno))))
    (labels ((now () (get-internal-real-time))
             (remaining () (/ (- deadline (now)) (float itu)))
             (pending () (- launched collected))
             (more-p () (and (< launched *pool-max-attempts*) (> (remaining) 0.2) (%pool-alive-upstreams pool tried)))
             (launch (up)
               (push up tried) (incf launched) (setf last-launch (now))
               (let ((limit (max 0.5 (remaining))))
                 (sb-thread:make-thread
                  (lambda ()
                    (multiple-value-bind (a kind) (%pool-attempt pool up method wait fn-octets started limit)
                      (sb-thread:with-mutex (lock) (push (list up a kind) results))
                      (sb-thread:signal-semaphore sem)))
                  :name (format nil "pool attempt ~A" (pool-upstream-name up)))))
             (launch-next ()
               (let ((up (and (more-p) (%pool-select pool wait-seqno tried))))
                 (when up (launch up) t)))
             (finish ()
               (return-from %pool-race (values answer (and (not answer) failure)))))
      (let ((first (or (%pool-select pool wait-seqno nil)
                       ;; every session is down: open the standbys, give the sessions a moment to come up
                       (progn (%pool-activate-standby pool (upstream-pool-max-active pool))
                              (loop repeat (round (* 10 *pool-startup-grace*))
                                    do (let ((up (%pool-select pool wait-seqno nil))) (when up (return up)))
                                       (when (upstream-pool-stopped pool) (return nil))
                                       (sleep 0.1))))))
        (unless first (return-from %pool-race (values nil :no-server)))
        (launch first))
      (loop
        (let* ((hedgeable (and hedge (more-p)))
               (to-hedge (and hedgeable (/ (- (+ last-launch (round (* hedge itu))) (now)) (float itu))))
               (wait-for (max 0.01 (if hedgeable (min (remaining) to-hedge) (remaining)))))
          (if (sb-thread:wait-on-semaphore sem :timeout wait-for)
              (let ((batch (sb-thread:with-mutex (lock) (prog1 (reverse results) (setf results '())))))
                ;; the semaphore was decremented once; account for the further results already queued
                (loop repeat (1- (length batch)) do (sb-thread:try-semaphore sem))
                (dolist (r batch)
                  (destructuring-bind (up a kind) r
                    (incf collected)
                    (case kind
                      ((nil) (%pool-remember-answer pool a up) (return-from %pool-race (values a nil)))
                      (:error (setf answer a)
                       (unless history (return-from %pool-race (values a nil)))
                       (launch-next))
                      (:notready (setf answer a) (launch-next))
                      (t (setf failure kind) (launch-next)))))
                (when (and (zerop (pending)) (not (more-p))) (finish)))
              (cond ((<= (remaining) 0.0) (finish))
                    (hedgeable (launch-next))))
          (when (and (<= (remaining) 0.0) (zerop (pending))) (finish))
          (when (<= (remaining) -1.0) (finish)))))))

(defun upstream-pool-send-query (pool payload timeout)
  "ADNL-EXT-CLIENT-SEND-QUERY for the whole pool: PAYLOAD is the octets of a liteServer.query (an optional waitMasterchainSeqno prefix
and the function); returns the octets of the answer, TIMEOUT seconds at most in all.  Signals ADNL-NOT-READY when no upstream is up,
ADNL-CLOSED when the connections were lost, ADNL-TIMEOUT when nobody answered in time."
  (let ((started (get-internal-real-time))
        (outer (tl-decode payload)))
    (unless (tl-is outer "liteServer.query") (error 'ton-error :format-control "the pool sends liteServer.query payloads only"))
    (multiple-value-bind (wait fn-octets) (proxy-split-query (tl-get outer :data))
      (let* ((q (proxy-query-info (%decode-function fn-octets))) (method (qinfo-name q)))
        (multiple-value-bind (answer failure)
            (%pool-race pool method (proxy-history-query-p q) wait fn-octets timeout started)
          (cond (answer answer)
                ((eq failure :no-server)
                 (error 'adnl-not-ready :format-control "no liteserver is up for ~A" :format-arguments (list method)))
                ((eq failure :dead)
                 (error 'adnl-closed :format-control "the liteservers lost their connections during ~A" :format-arguments (list method)))
                (t (error 'adnl-timeout :format-control "no liteserver answered ~A within ~As" :format-arguments (list method timeout)))))))))

;;; verdicts

(defun %pool-reject-upstream (pool up)
  "Avoid UP for a ban that doubles with each report close to the last one."
  (sb-thread:with-mutex ((upstream-pool-lock pool))
    (let ((now (get-internal-real-time)))
      (when (> (- now (pool-upstream-ban-until up)) (* 3600 internal-time-units-per-second))
        (setf (pool-upstream-reject-streak up) 0))
      (let* ((streak (incf (pool-upstream-reject-streak up)))
             (seconds (min *pool-rejection-ban-max* (* *pool-rejection-ban* (expt 2 (min 10 (1- streak)))))))
        (setf (pool-upstream-ban-until up) (max (pool-upstream-ban-until up) (+ now (* seconds internal-time-units-per-second))))))))

(defun upstream-pool-apply-verdict (pool answer-hash accepted)
  "The client says the answer whose octets hash to ANSWER-HASH (SHA-256) verified (ACCEPTED) or did not.  An answer that did not
verify bans the upstream that gave it for a while.  True when the answer is one the pool remembers."
  (let ((up (sb-thread:with-mutex ((upstream-pool-lock pool))
              (gethash (octets->hex answer-hash) (upstream-pool-answer-origins pool)))))
    (when up
      (unless accepted (%pool-reject-upstream pool up))
      t)))
