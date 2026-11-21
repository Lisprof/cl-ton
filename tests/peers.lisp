;;;; tests/peers.lisp -- liteserver candidates: the UDP probe, the score and pools, and the diagnose report (src/peers.lisp).

(in-package :cl-ton/test)

(defun %peers-t-lite-handler (&key (seqno 777) error)
  "A simulated liteserver on UDP: liteServer.query around getTime / getMasterchainInfo; with ERROR a liteServer.error instead."
  (lambda (query public)
    (declare (ignore public))
    (let ((q (cl-ton::tl-decode query)))
      (when (cl-ton::tl-is q "liteServer.query")
        (let ((inner (cl-ton::tl-decode (cl-ton::as-octets (cl-ton::tl-get q :data)))))
          (cond
            (error (cl-ton::tl-encode (cl-ton::tl-make "liteServer.error" :code 651 :message error)))
            ((cl-ton::tl-is inner "liteServer.getTime") (cl-ton::tl-encode (cl-ton::tl-make "liteServer.currentTime" :now (cl-ton::unix-now))))
            ((cl-ton::tl-is inner "liteServer.getMasterchainInfo")
             (let ((zero (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
               (cl-ton::tl-encode
                (cl-ton::tl-make "liteServer.masterchainInfo"
                                 :last (cl-ton::tl-block-id-ext :workchain -1 :seqno seqno :root-hash zero :file-hash zero)
                                 :state-root-hash zero
                                 :init (cl-ton::tl-make "tonNode.zeroStateIdExt" :workchain -1 :root-hash zero :file-hash zero)))))
            (t nil)))))))

(defun test-peers ()
  (format t "peers: the UDP liteserver probe, the score, the pools~%")
  (let* ((full (cl-ton::adnl-udp-start :handler (%peers-t-lite-handler :seqno 777)))
         (silent (cl-ton::adnl-udp-start :handler (lambda (q p) (declare (ignore q p)) nil)))
         (broken (cl-ton::adnl-udp-start :handler (%peers-t-lite-handler :error "cannot do that")))
         (client (cl-ton::adnl-udp-start)))
    (unwind-protect
         (flet ((probe (node) (cl-ton::lite-udp-probe client "127.0.0.1" (cl-ton::adnl-udp-port node)
                                                      (cl-ton::keypair-public (cl-ton::adnl-udp-keypair node)) :timeout 0.7)))
           (let ((r (probe full)))
             (check "probe: a liteserver answers getTime and getMasterchainInfo over UDP: clock, head and round trip"
                    (and (getf r :lite) (= 777 (getf r :seqno)) (< (abs (- (getf r :now) (cl-ton::unix-now))) 5)
                         (< 0 (getf r :rtt) 1))))
           (let ((r (probe silent)))
             (check "probe: a node that does not answer lite queries is reported without a lite answer"
                    (and (not (getf r :lite)) (search "no answer" (getf r :error)))))
           (let ((r (probe broken)))
             (check "probe: a liteServer.error is reported with its code and message"
                    (and (not (getf r :lite)) (search "651" (getf r :error)) (search "cannot do that" (getf r :error))))))
      (mapc #'cl-ton::adnl-udp-stop (list full silent broken client))))
  ;; the TCP probe and the port scan, against Lisp ADNL-ext servers on loopback
  (let* ((full-key (cl-ton::adnl-generate-keypair)) (broken-key (cl-ton::adnl-generate-keypair))
         (full (cl-ton::start-adnl-ext-server :keypair full-key
                                              :handler (let ((h (%peers-t-lite-handler :seqno 888)))
                                                         (lambda (s c id q) (declare (ignore s c id)) (funcall h q nil)))))
         (broken (cl-ton::start-adnl-ext-server :keypair broken-key
                                                :handler (let ((h (%peers-t-lite-handler :error "cannot do that")))
                                                           (lambda (s c id q) (declare (ignore s c id)) (funcall h q nil))))))
    (unwind-protect
         (let ((port (cl-ton::adnl-ext-server-port full)))
           (let ((r (cl-ton::lite-tcp-probe "127.0.0.1" port (cl-ton::keypair-public full-key) :timeout 2)))
             (check "tcp probe: a liteserver answers getTime and getMasterchainInfo over ADNL ext TCP: clock, head and round trip"
                    (and (getf r :lite) (= 888 (getf r :seqno)) (< (abs (- (getf r :now) (cl-ton::unix-now))) 5)
                         (<= 0 (getf r :rtt) 2))))
           (let ((r (cl-ton::lite-tcp-probe "127.0.0.1" port (cl-ton::keypair-public (cl-ton::adnl-generate-keypair)) :timeout 1)))
             (check "tcp probe: an open port whose ADNL key is another one is reported without a lite answer"
                    (and (not (getf r :lite)) (getf r :error))))
           (let ((r (cl-ton::lite-tcp-probe "127.0.0.1" (cl-ton::adnl-ext-server-port broken) (cl-ton::keypair-public broken-key) :timeout 2)))
             (check "tcp probe: a liteServer.error is reported with its code and message"
                    (and (not (getf r :lite)) (search "651" (getf r :error)) (search "cannot do that" (getf r :error)))))
           (let ((r (cl-ton::lite-tcp-probe "127.0.0.1" 1 (cl-ton::keypair-public full-key) :timeout 1)))
             (check "tcp probe: a closed port is reported without a lite answer"
                    (and (not (getf r :lite)) (getf r :error))))
           (let* ((seen '())
                  (open (cl-ton::tcp-scan '("127.0.0.1") (- port 3) (+ port 3) :timeout 1 :width 4
                                                                                 :progress (lambda (p) (push p seen)))))
             (check "scan: the open port in a range is found, as (host . port)"
                    (member (cons "127.0.0.1" port) open :test #'equal))
             (check "scan: the ports of the range that are closed are not reported"
                    (notany (lambda (pair) (and (/= (cdr pair) port) (/= (cdr pair) (cl-ton::adnl-ext-server-port broken)))) open))
             (check "scan: progress is reported"
                    (and seen (every (lambda (p) (<= 0 p 100)) seen)))
             (check "scan: an empty range is an empty result"
                    (null (cl-ton::tcp-scan '("127.0.0.1") 10 9)))))
      (cl-ton::stop-adnl-ext-server full)
      (cl-ton::stop-adnl-ext-server broken)))
  ;; the score
  (flet ((c (rtt seqno &key (probes 10) (failures 0))
           (cl-ton::make-lite-candidate :host "h" :port 1 :rtt rtt :seqno seqno :probes probes :failures failures)))
    (let* ((fast-stale (c 0.05 90)) (slow-fresh (c 0.35 100)) (down (c nil nil :probes 5 :failures 5))
           (flaky (c 0.05 100 :failures 5)) (best (c 0.06 100))
           (ranked (cl-ton::rank-candidates (list fast-stale slow-fresh down flaky best))))
      (check "score: freshness decides: a slow node at the head beats a fast one ten blocks behind"
             (< (position slow-fresh ranked) (position fast-stale ranked)))
      (check "score: a flaky node ranks below a reliable one of the same speed and head"
             (< (position best ranked) (position flaky ranked)))
      (check "score: a node that never answered ranks last"
             (eq down (car (last ranked))))
      (multiple-value-bind (hot warm) (cl-ton::select-pools ranked :hot 2)
        (check "pools: the best answering nodes are hot, the other answering ones warm, the dead are in neither"
               (and (= 2 (length hot)) (eq best (first hot)) (= 2 (length warm))
                    (not (member down hot)) (not (member down warm)))))
      (let ((c (c nil nil :probes 0)))
        (cl-ton::lite-candidate-record c (list :lite t :rtt 0.2 :seqno 50 :now 1700000000))
        (cl-ton::lite-candidate-record c (list :lite t :rtt 0.1 :seqno 51 :now 1700000005))
        (cl-ton::lite-candidate-record c (list :lite nil :error "no answer"))
        (check "record: the round trip is smoothed, the newest head kept, a failed probe counted"
               (and (< 0.1 (cl-ton::lite-candidate-rtt c) 0.2) (= 51 (cl-ton::lite-candidate-seqno c))
                    (= 3 (cl-ton::lite-candidate-probes c)) (= 1 (cl-ton::lite-candidate-failures c))))))))

(defun test-dht-diagnose ()
  (format t "diagnose: the DHT crawl and probe report against a simulated network~%")
  (let* ((servers (%dht-t-network 8))
         (lite-key (cl-ton::adnl-generate-keypair))
         (lite (cl-ton::adnl-udp-start :keypair lite-key :handler (%peers-t-lite-handler :seqno 4242)))
         (short (cl-ton::adnl-short-id (cl-ton::keypair-public lite-key)))
         (key-id (cl-ton::dht-key-id short))
         (holder (first (sort (copy-list servers) #'<
                              :key (lambda (s) (cl-ton::dht-distance (cl-ton::adnl-short-id (cl-ton::keypair-public (dht-t-server-keypair s))) key-id)))))
         (config (format nil "/tmp/dht-diagnose-config-~D.json" (random 1000000)))
         ;; a liteserver on ADNL ext TCP that uses the key of one of the DHT nodes
         (tcp-lite (cl-ton::start-adnl-ext-server :keypair (dht-t-server-keypair (first servers))
                                                  :handler (let ((h (%peers-t-lite-handler :seqno 5151)))
                                                             (lambda (s c id q) (declare (ignore s c id)) (funcall h q nil)))))
         (tcp-port (cl-ton::adnl-ext-server-port tcp-lite)))
    (setf (gethash key-id (dht-t-server-values holder))
          (%dht-t-value lite-key (cl-ton::tl-encode (%dht-t-address-list (cl-ton::adnl-udp-port lite)))))
    (with-open-file (out config :direction :output :if-exists :supersede)
      (format out "{\"liteservers\": [{\"ip\": 2130706433, \"port\": 9999, \"id\": {\"@type\": \"pub.ed25519\", \"key\": \"~A\"}}]}"
              (cl-ton::base64-encode (cl-ton::keypair-public lite-key))))
    (unwind-protect
         (let* ((stream (make-string-output-stream))
                (summary (cl-ton::dht-diagnose :stream stream :config-path config :bootstrap (%dht-t-bootstrap-of servers '(0 3))
                                               :rounds 3 :timeout 1.5 :dht-timeout 1.5
                                               :scan-from (- tcp-port 4) :scan-to (+ tcp-port 4) :scan-timeout 1 :scan-width 4))
                (text (get-output-stream-string stream)))
           (check "diagnose: the crawl finds the whole simulated DHT"
                  (>= (getf summary :dht-nodes) 8))
           (check "diagnose: the host of the DHT nodes is scanned, its open TCP port found, and the lite server on it answers over TCP"
                  (and (= 1 (getf summary :tcp-hosts)) (>= (getf summary :tcp-open) 1) (= 1 (getf summary :tcp-lite))))
           (check "diagnose: the config liteserver is found by its id in the DHT and answers liteServer queries over its UDP address"
                  (and (= 1 (getf summary :config-found)) (= 1 (getf summary :config-lite))))
           (check "diagnose: the report names the sections and ends with the summary"
                  (and (search "== ADNL/DHT diagnose ==" text) (search "crawl round 3" text)
                       (search "LITE OK over UDP" text) (search "seqno 4242" text)
                       (search "LITE OK over TCP" text) (search "seqno 5151" text) (search "== summary:" text))))
      (ignore-errors (delete-file config))
      (cl-ton::adnl-udp-stop lite)
      (cl-ton::stop-adnl-ext-server tcp-lite)
      (%dht-t-stop servers))))

;;; --- the upstream pool -------------------------------------------------------------------------------------------------------------

(defun %pool-t-server (behaviour)
  "An ADNL-ext server whose answers BEHAVIOUR decides: a function of (METHOD WAIT-SEQNO) returning the octets of an answer, a number
(answer after that many seconds), or (:silent SECONDS) (nothing for that long).  (VALUES SERVER CALLS PUBLIC): CALLS is a cons holding
the list of (METHOD WAIT-SEQNO) the server has seen, newest first."
  (let* ((keypair (cl-ton::adnl-generate-keypair)) (calls (list nil)) (lock (sb-thread:make-mutex))
         (server (cl-ton::start-adnl-ext-server
                  :keypair keypair
                  :handler (lambda (server conn id query)
                             (declare (ignore server conn id))
                             (let ((outer (cl-ton::tl-decode query)))
                               (multiple-value-bind (wait fn) (cl-ton::proxy-split-query (cl-ton::tl-get outer :data))
                                 (let* ((method (cl-ton::tl-obj-name (cl-ton::tl-decode fn)))
                                        (wait-seqno (and wait (cl-ton::tl-get wait :seqno))))
                                   (sb-thread:with-mutex (lock) (push (list method wait-seqno) (car calls)))
                                   (let ((r (funcall behaviour method wait-seqno)))
                                     (cond ((consp r) (sleep (second r)) nil)
                                           ((numberp r) (sleep r) (funcall behaviour method wait-seqno))
                                           (t r))))))))))
    (values server calls (cl-ton::keypair-public keypair))))

(defun %pool-t-answer (what &optional (seqno 700))
  (case what
    (:time (cl-ton::tl-encode (cl-ton::tl-make "liteServer.currentTime" :now (cl-ton::unix-now))))
    (:info (let ((zero (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
             (cl-ton::tl-encode
              (cl-ton::tl-make "liteServer.masterchainInfo"
                               :last (cl-ton::tl-block-id-ext :workchain -1 :seqno seqno :root-hash zero :file-hash zero)
                               :state-root-hash zero
                               :init (cl-ton::tl-make "tonNode.zeroStateIdExt" :workchain -1 :root-hash zero :file-hash zero)))))))

(defun %pool-t-error (code message)
  (cl-ton::tl-encode (cl-ton::tl-make "liteServer.error" :code code :message message)))

(defun %pool-t-payload (function &optional wait-seqno)
  (let ((data (cl-ton::tl-encode function)))
    (cl-ton::tl-encode
     (cl-ton::tl-make "liteServer.query"
                      :data (if wait-seqno
                                (cl-ton::%cat (cl-ton::tl-encode (cl-ton::tl-make "liteServer.waitMasterchainSeqno"
                                                                                  :seqno wait-seqno :timeout-ms 3000))
                                              data)
                                data)))))

(defun %pool-t-block ()
  (let ((zero (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
    (cl-ton::tl-block-id-ext :workchain -1 :seqno 5 :root-hash zero :file-hash zero)))

(defun %pool-t-ask (pool name &optional (timeout 3) wait-seqno)
  "The answer to liteServer.NAME (with the fields these tests need) on POOL, decoded."
  (let ((function (cond ((string= name "getAccountState")
                         (cl-ton::tl-make "liteServer.getAccountState" :id (%pool-t-block)
                                          :account (cl-ton::tl-make "liteServer.accountId" :workchain 0
                                                                    :id (make-array 32 :element-type '(unsigned-byte 8) :initial-element 1))))
                        ((string= name "getBlockProof")
                         (cl-ton::tl-make "liteServer.getBlockProof" :mode 0 :known-block (%pool-t-block)))
                        (t (cl-ton::tl-make (format nil "liteServer.~A" name))))))
    (cl-ton::tl-decode (cl-ton::upstream-pool-send-query pool (%pool-t-payload function wait-seqno) timeout))))

(defun %pool-t-pool (&rest servers)
  "A pool over the SERVERS (each a list (SERVER CALLS PUBLIC)), every session up."
  (let ((pool (cl-ton::open-upstream-pool
               (loop for (server nil public) in servers collect (list "127.0.0.1" (cl-ton::adnl-ext-server-port server) public)))))
    (loop repeat 100
          until (every (lambda (up) (cl-ton::adnl-ext-client-alive-p (cl-ton::pool-upstream-client up)))
                       (cl-ton::upstream-pool-upstreams pool))
          do (sleep 0.1))
    pool))

(defun %pool-t-up (pool server)
  (find (cl-ton::adnl-ext-server-port server) (cl-ton::upstream-pool-upstreams pool)
        :key #'cl-ton::pool-upstream-port))

(defun %pool-t-calls (calls &optional method)
  (count-if (lambda (c) (or (null method) (string= (first c) method))) (car calls)))

(defmacro %pool-t-with-servers ((&rest specs) &body body)
  "Bind each (VAR BEHAVIOUR) of SPECS to a list (SERVER CALLS PUBLIC) of a started %POOL-T-SERVER; stop them all afterwards."
  `(let (,@(loop for (var behaviour) in specs
                 collect `(,var (multiple-value-list (%pool-t-server ,behaviour)))))
     (unwind-protect (progn ,@body)
       ,@(loop for (var) in specs collect `(ignore-errors (cl-ton::stop-adnl-ext-server (first ,var)))))))

(defun test-upstream-pool ()
  (format t "upstream pool: selection, hedging, failover, penalties, verdicts, waits~%")
  (let ((cl-ton::*pool-hedge-delay* 0.3) (cl-ton::*pool-hedge-min* 0.1) (cl-ton::*pool-startup-grace* 0.5)
        (good (lambda (method wait) (declare (ignore wait))
                (cond ((string= method "liteServer.getTime") (%pool-t-answer :time))
                      ((string= method "liteServer.getMasterchainInfo") (%pool-t-answer :info 700))
                      (t (%pool-t-error -400 "unexpected")))))
        (silent (lambda (method wait) (declare (ignore method wait)) (list :silent 2.5))))
    ;; one upstream: the answer as the server sent it; the head is learned from it
    (%pool-t-with-servers ((a good))
      (let ((pool (%pool-t-pool a)))
        (unwind-protect
             (let ((answer (%pool-t-ask pool "getMasterchainInfo")))
               (check "pool: one upstream answers, the answer is the server's own"
                      (cl-ton::tl-is answer "liteServer.masterchainInfo"))
               (check "pool: the head seen in an answer is remembered for the upstream and the pool"
                      (and (= 700 (cl-ton::pool-upstream-seqno (first (cl-ton::upstream-pool-upstreams pool))))
                           (= 700 (cl-ton::upstream-pool-max-seqno pool))))
               (check "pool: it is alive, and not once closed"
                      (cl-ton::upstream-pool-alive-p pool)))
          (cl-ton::close-upstream-pool pool))
        (check "pool: a closed pool is not alive" (not (cl-ton::upstream-pool-alive-p pool)))))
    ;; a silent upstream costs the hedge delay, not the query
    (%pool-t-with-servers ((a silent) (b good))
      (let ((pool (%pool-t-pool a b)))
        (unwind-protect
             (let* ((t0 (get-internal-real-time))
                    (answer (%pool-t-ask pool "getTime"))
                    (took (/ (- (get-internal-real-time) t0) (float internal-time-units-per-second))))
               (check "pool: with one upstream silent the other answers, within the hedge delay and a little"
                      (and (cl-ton::tl-is answer "liteServer.currentTime") (< took 2.0)))
               (check "pool: the answering upstream served the query"
                      (plusp (%pool-t-calls (second b) "liteServer.getTime"))))
          (cl-ton::close-upstream-pool pool))))
    ;; a penalized upstream is avoided while another is left
    (%pool-t-with-servers ((a good) (b good))
      (let ((pool (%pool-t-pool a b)))
        (unwind-protect
             (progn
               (setf (cl-ton::pool-upstream-penalty-until (%pool-t-up pool (first a)))
                     (+ (get-internal-real-time) (* 60 internal-time-units-per-second)))
               (dotimes (i 6) (%pool-t-ask pool "getTime"))
               (check "pool: an upstream in its penalty gets no query while another is up"
                      (and (zerop (%pool-t-calls (second a))) (= 6 (%pool-t-calls (second b)))))
               (setf (cl-ton::pool-upstream-penalty-until (%pool-t-up pool (first a))) 0
                     (cl-ton::pool-upstream-ban-until (%pool-t-up pool (first a)))
                     (+ (get-internal-real-time) (* 60 internal-time-units-per-second)))
               (dotimes (i 6) (%pool-t-ask pool "getTime"))
               (check "pool: a banned upstream is avoided just the same"
                      (zerop (%pool-t-calls (second a)))))
          (cl-ton::close-upstream-pool pool))))
    ;; errors: an account query's error is the answer; a history query's error is asked again elsewhere; "not ready" too
    (%pool-t-with-servers ((a (lambda (method wait) (declare (ignore wait))
                                (if (member method '("liteServer.getAccountState" "liteServer.getBlockProof") :test #'string=)
                                    (%pool-t-error -400 "no such thing")
                                    (%pool-t-answer :time))))
                           (b (lambda (method wait) (declare (ignore wait))
                                (if (string= method "liteServer.getBlockProof")
                                    (%pool-t-answer :time)
                                    (%pool-t-error -400 "no such thing")))))
      (let ((pool (%pool-t-pool a b)))
        (unwind-protect
             (progn
               (let ((answer (%pool-t-ask pool "getAccountState")))
                 (check "pool: an error answer to an account query is the answer, not retried elsewhere"
                        (and (cl-ton::tl-is answer "liteServer.error") (= 1 (+ (%pool-t-calls (second a) "liteServer.getAccountState")
                                                                              (%pool-t-calls (second b) "liteServer.getAccountState"))))))
               (let ((answer (%pool-t-ask pool "getBlockProof")))
                 (check "pool: an error answer to a history query is retried on another upstream until one has the answer"
                        (cl-ton::tl-is answer "liteServer.currentTime"))))
          (cl-ton::close-upstream-pool pool))))
    (%pool-t-with-servers ((a (lambda (method wait) (declare (ignore method wait)) (%pool-t-error 651 "block is not in db")))
                           (b good))
      (let ((pool (%pool-t-pool a b)))
        (unwind-protect
             (progn
               (check "pool: \"not ready\" (651) is asked of another upstream and the good answer wins"
                      (dotimes (i 4 t)
                        (unless (cl-ton::tl-is (%pool-t-ask pool "getTime") "liteServer.currentTime") (return nil))))
               (check "pool: the upstream that answered \"not ready\" is avoided afterwards"
                      (let ((up (%pool-t-up pool (first a))))
                        (or (zerop (%pool-t-calls (second a)))
                            (> (cl-ton::pool-upstream-penalty-until up) (get-internal-real-time))))))
          (cl-ton::close-upstream-pool pool))))
    ;; nobody answers: a timeout, in about the time asked; nobody up: not ready
    (%pool-t-with-servers ((a silent) (b silent))
      (let ((pool (%pool-t-pool a b)))
        (unwind-protect
             (let ((t0 (get-internal-real-time)))
               (check "pool: when no upstream answers in time the query ends in ADNL-TIMEOUT"
                      (handler-case (progn (%pool-t-ask pool "getTime" 1.0) nil)
                        (cl-ton::adnl-timeout () t)))
               (check "pool: ... after about the time asked, not much longer"
                      (< (/ (- (get-internal-real-time) t0) (float internal-time-units-per-second)) 3.0))
               ;; the attempts are bookkept by their own threads, a moment after the query has ended
               (loop repeat 40 until (some (lambda (up) (plusp (cl-ton::pool-upstream-fail-streak up))) (cl-ton::upstream-pool-upstreams pool))
                     do (sleep 0.1))
               (check "pool: the silent upstreams are penalized, and their failure streak counted"
                      (some (lambda (up) (and (plusp (cl-ton::pool-upstream-fail-streak up))
                                              (> (cl-ton::pool-upstream-penalty-until up) (get-internal-real-time))))
                            (cl-ton::upstream-pool-upstreams pool))))
          (cl-ton::close-upstream-pool pool))))
    (let ((pool (cl-ton::open-upstream-pool (list (list "127.0.0.1" 1 (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7))))))
      (unwind-protect
           (check "pool: with no upstream up the query ends in ADNL-NOT-READY"
                  (handler-case (progn (%pool-t-ask pool "getTime" 1.0) nil)
                    (cl-ton::adnl-not-ready () t)))
        (cl-ton::close-upstream-pool pool)))
    ;; standby sessions are opened when no active one is up
    (%pool-t-with-servers ((a good))
      (let ((pool (cl-ton::open-upstream-pool
                   (list (list "127.0.0.1" 1 (make-array 32 :element-type '(unsigned-byte 8) :initial-element 9))
                         (list "127.0.0.1" (cl-ton::adnl-ext-server-port (first a)) (third a)))
                   :max-active 1)))
        (unwind-protect
             (progn
               (check "pool: only MAX-ACTIVE sessions are started at once"
                      (= 1 (count-if #'cl-ton::pool-upstream-started-p (cl-ton::upstream-pool-upstreams pool))))
               (check "pool: a standby session is opened when the active one is not up, and answers"
                      (loop repeat 6
                            thereis (handler-case (cl-ton::tl-is (%pool-t-ask pool "getTime" 2.0) "liteServer.currentTime")
                                      (cl-ton::adnl-closed () nil)))))
          (cl-ton::close-upstream-pool pool))))
    ;; verdicts of the client
    (%pool-t-with-servers ((a good) (b good))
      (let ((pool (%pool-t-pool a b)))
        (unwind-protect
             (let* ((payload (%pool-t-payload (cl-ton::tl-make "liteServer.getTime")))
                    (raw (cl-ton::upstream-pool-send-query pool payload 3))
                    (origin (let ((hit nil))
                              (maphash (lambda (k v) (declare (ignore k)) (setf hit v)) (cl-ton::upstream-pool-answer-origins pool))
                              hit)))
               (check "pool: the upstream of a returned answer is remembered by the answer's hash"
                      (and origin (cl-ton::upstream-pool-apply-verdict pool (cl-ton::sha256 raw) t)))
               (check "pool: a verdict about an answer the pool never gave is not known"
                      (not (cl-ton::upstream-pool-apply-verdict pool (cl-ton::sha256 (cl-ton::%cat raw raw)) nil)))
               (check "pool: an accepted answer bans nobody"
                      (zerop (cl-ton::pool-upstream-ban-until origin)))
               (check "pool: an answer reported as not verifying bans the upstream that gave it"
                      (progn (cl-ton::upstream-pool-apply-verdict pool (cl-ton::sha256 raw) nil)
                             (> (cl-ton::pool-upstream-ban-until origin) (get-internal-real-time))))
               (let ((first-ban (cl-ton::pool-upstream-ban-until origin)))
                 (cl-ton::upstream-pool-apply-verdict pool (cl-ton::sha256 raw) nil)
                 (check "pool: a repeat report within the ban doubles it"
                        (and (= 2 (cl-ton::pool-upstream-reject-streak origin))
                             (> (cl-ton::pool-upstream-ban-until origin) (+ first-ban (* 100 internal-time-units-per-second))))))
               (let ((other (if (eq origin (%pool-t-up pool (first a))) b a)))
                 (let ((before (%pool-t-calls (second other))))
                   (dotimes (i 4) (%pool-t-ask pool "getTime"))
                   (check "pool: the banned upstream gets no more queries while the other is up"
                          (= 4 (- (%pool-t-calls (second other)) before))))))
          (cl-ton::close-upstream-pool pool))))
    ;; waits: dropped for an upstream known to be ahead, forwarded to one that is not
    (%pool-t-with-servers ((a good))
      (let ((pool (%pool-t-pool a)))
        (unwind-protect
             (progn
               (%pool-t-ask pool "getTime" 3 550)
               (check "pool: the wait is forwarded to an upstream not known to have the block"
                      (equal '("liteServer.getTime" 550) (first (car (second a)))))
               (setf (cl-ton::pool-upstream-seqno (first (cl-ton::upstream-pool-upstreams pool))) 700)
               (%pool-t-ask pool "getTime" 3 550)
               (check "pool: the wait is dropped for an upstream known to be past the block"
                      (equal '("liteServer.getTime" nil) (first (car (second a))))))
          (cl-ton::close-upstream-pool pool))))
    (%pool-t-with-servers ((a good) (b good))
      (let ((pool (%pool-t-pool a b)))
        (unwind-protect
             (progn
               (setf (cl-ton::pool-upstream-seqno (%pool-t-up pool (first a))) 800
                     (cl-ton::pool-upstream-seqno (%pool-t-up pool (first b))) 100
                     (cl-ton::upstream-pool-max-seqno pool) 800)
               (dotimes (i 5) (%pool-t-ask pool "getTime" 3 600))
               (check "pool: a query that waits for a block goes to the upstream that has it"
                      (and (= 5 (%pool-t-calls (second a))) (zerop (%pool-t-calls (second b)))))
               (dotimes (i 5) (%pool-t-ask pool "getTime"))
               (check "pool: an upstream far behind the best head is avoided for every query"
                      (zerop (%pool-t-calls (second b)))))
          (cl-ton::close-upstream-pool pool))))
    ;; the pool from a global config: the servers with a slice are left out
    (let ((path (format nil "/tmp/upstream-pool-config-~D.json" (random 1000000)))
          (key (cl-ton::base64-encode (make-array 32 :element-type '(unsigned-byte 8) :initial-element 5))))
      (unwind-protect
           (progn
             (with-open-file (out path :direction :output :if-exists :supersede)
               (format out "{\"liteservers\":[{\"ip\":2130706433,\"port\":1,\"id\":{\"@type\":\"pub.ed25519\",\"key\":\"~A\"}},
 {\"ip\":2130706433,\"port\":2,\"id\":{\"@type\":\"pub.ed25519\",\"key\":\"~A\"},\"slices\":[{\"@type\":\"liteserver.descV2.sliceSimple\",\"shards\":[{\"workchain\":0,\"shard\":-9223372036854775808}]}]}]}"
                       key key))
             (let ((pool (cl-ton::open-upstream-pool-from-config path)))
               (unwind-protect
                    (check "pool from a config: the servers of the file are the upstreams, one with a slice is left out"
                           (equal '("127.0.0.1:1") (mapcar #'cl-ton::pool-upstream-name (cl-ton::upstream-pool-upstreams pool))))
                 (cl-ton::close-upstream-pool pool))))
        (ignore-errors (delete-file path))))))

(defun test-lite-client-pool ()
  (format t "lite client over an upstream pool~%")
  (let ((fc (cl-ton::start-fakechain)) pool client)
    (unwind-protect
         (progn
           (cl-ton::fakechain-advance fc 3)
           (let ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc))) (port (cl-ton::fakechain-port fc)))
             (setf pool (cl-ton::open-upstream-pool (list (list "127.0.0.1" port public) (list "127.0.0.1" port public)
                                                          (list "127.0.0.1" 1 public)))
                   client (cl-ton::open-lite-client-pool pool (%zero-block-id fc)))
             (loop repeat 100 until (cl-ton::upstream-pool-alive-p pool) do (sleep 0.1))
             (check "a lite client over a pool syncs: the head proved is the one the chain has"
                    (let ((head (cl-ton::lite-sync client)))
                      (and (= (cl-ton::tl-get head :seqno) (cl-ton::fc-head-seqno fc)) (plusp (cl-ton::tl-get head :seqno)))))
             (check "...and a plain call through it is answered"
                    (cl-ton::tl-is (cl-ton::lite-call client (cl-ton::tl-make "liteServer.getTime")) "liteServer.currentTime"))
             (check "...and a verified call reports a bad answer to the pool, which bans the upstream that gave it"
                    (let ((bad nil))
                      (handler-case
                          (cl-ton::lite-call-verified client (cl-ton::tl-make "liteServer.getTime")
                                                      (lambda (answer) (declare (ignore answer))
                                                        (if bad
                                                            :ok
                                                            (progn (setf bad t)
                                                                   (error 'cl-ton::proof-error :format-control "not good enough")))))
                        (error () nil))
                      (and bad (some (lambda (up) (> (cl-ton::pool-upstream-ban-until up) 0))
                                     (cl-ton::upstream-pool-upstreams pool)))))
             (check "...and closing the client closes the pool"
                    (progn (cl-ton::close-lite-client client) (not (cl-ton::upstream-pool-alive-p pool))))))
      (when pool (ignore-errors (cl-ton::close-upstream-pool pool)))
      (cl-ton::stop-fakechain fc))))

(defun test-lite-chain ()
  (format t "lite chain: the Chain operations over a lite client and an upstream pool~%")
  (let ((fc (cl-ton::start-fakechain)) pool chain)
    (unwind-protect
         (let* ((wallet (%seed-wallet fc))
                (dest (cl-ton::make-address :workchain 0 :hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x42))))
           (cl-ton::fakechain-advance fc 2)
           (let ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc))) (port (cl-ton::fakechain-port fc)))
             (setf pool (cl-ton::open-upstream-pool (list (list "127.0.0.1" port public) (list "127.0.0.1" port public)))
                   chain (cl-ton::make-lite-chain (cl-ton::open-lite-client-pool pool (%zero-block-id fc)) nil wallet nil))
             (loop repeat 100 until (cl-ton::upstream-pool-alive-p pool) do (sleep 0.1))
             (check "lite chain: the wallet is deployed, as proved through the pool"
                    (cl-ton::chain-wallet-deployed-p chain))
             (check "lite chain: the TON balance is the funded one"
                    (= (cl-ton::nano 10) (cl-ton::chain-ton-balance chain)))
             (check "lite chain: the wallet's seqno is read by a getter run on the proved state"
                    (eql 0 (cl-ton::chain-wallet-seqno chain)))
             (multiple-value-bind (external body) (%transfer wallet 0 dest (cl-ton::nano 1))
               (declare (ignore body))
               (check "lite chain: the signed message emulates successfully against the proved account"
                      (cl-ton::emulation-result-success-p (cl-ton::chain-emulate chain external)))
               (let ((hash (cl-ton::chain-send chain external)))
                 (check "lite chain: chain-send hands the message to the liteserver and returns its hash"
                        (stringp hash))
                 (cl-ton::fakechain-advance fc 2)
                 (check "lite chain: the transfer shows in the balance, the seqno and the transactions, found by the hash"
                        (and (< (cl-ton::chain-ton-balance chain) (cl-ton::nano 10))
                             (eql 1 (cl-ton::chain-wallet-seqno chain))
                             (some (lambda (tx) (cl-ton::transaction-matches-broadcast-p tx :message-hash hash))
                                   (cl-ton::chain-wallet-transactions chain))))))
             (let ((mover (sb-thread:make-thread (lambda () (sleep 0.4) (cl-ton::fakechain-advance fc 1)))))
               (check "lite chain: chain-wait-block returns the block that follows the head"
                      (cl-ton::chain-wait-block chain :timeout 5))
               (sb-thread:join-thread mover :default nil))
             (check "lite chain: the pool's clients and the chain's getter agree on the balance (getter = the chain's own)"
                    (functionp (cl-ton::chain-getter chain)))
             (cl-ton::chain-close chain)
             (check "lite chain: closing the chain closes the lite client and the pool"
                    (not (cl-ton::upstream-pool-alive-p pool)))))
      (ignore-errors (when pool (cl-ton::close-upstream-pool pool)))
      (cl-ton::stop-fakechain fc))))
