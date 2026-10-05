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

;;;; adnl-ext-client.lisp -- Phase C: one persistent outbound ADNL-ext session
;;;; to one upstream liteserver.
;;;;
;;;; Each ADNL-EXT-CLIENT owns a thread running a reconnect loop:
;;;;
;;;;     connect -> 256B init packet -> ciphers -> (ack) -> alive -> serve until
;;;;     the connection dies -> back off -> repeat
;;;;
;;;; SEND-QUERY wraps a payload in adnl.message.query with a fresh 256-bit
;;;; query id, parks the caller on a per-query semaphore in the pending table,
;;;; and returns the matching adnl.message.answer's payload VERBATIM (no
;;;; interpretation -- the proxy relays it, the caller decodes it).  A tcp.ping
;;;; goes out about every 10s; silence for several intervals is treated as a
;;;; dead connection and forces a reconnect.  tcp.authentificate is skipped.
;;;;
;;;; READY / NOT-READY callbacks feed the supervisor's per-server alive set.

(in-package :cl-ton)

(define-condition adnl-timeout (ton-error) ())
(define-condition adnl-not-ready (adnl-closed) ())

(defvar *adnl-log-function* nil
  "NIL, or a function of (control-string &rest args) receiving ADNL diagnostics.")

(defvar *adnl-log-lock* (sb-thread:make-mutex :name "adnl log")
  "Upstream threads log concurrently; without this their lines interleave mid-line.")

(defun adnl-log (control &rest args)
  (when *adnl-log-function*
    (sb-thread:with-recursive-lock (*adnl-log-lock*)
      (ignore-errors (apply *adnl-log-function* control args)))))

(defstruct (adnl-pending (:copier nil))
  (semaphore (sb-thread:make-semaphore))
  answer
  failure)

(defstruct (adnl-ext-client (:constructor %make-adnl-ext-client) (:copier nil))
  name host port server-public
  thread
  (stop-p nil)
  (conn nil)
  (ready-p nil)
  (lock (sb-thread:make-mutex :name "adnl-ext-client"))
  (pending (make-hash-table :test #'equal))
  on-ready on-not-ready
  (ping-interval 10)
  (silence-limit 35)
  (reconnect-delay 1)
  (last-rx 0)
  last-error
  (connects 0)
  ;; --- diagnostics (read with ADNL-EXT-CLIENT-STATUS) ---
  (stage :idle)                         ; :idle :tcp-connecting :tcp-connected :init-sent
                                        ; :ack-received :ready  (where the loop currently is)
  (stage-since 0)                       ; universal time of the last stage change
  (attempts 0)                          ; connection attempts started
  (failures 0)                          ; attempts / sessions that ended in an error
  last-failure                          ; (universal-time stage message hint) of the latest one
  (first-ready-at nil)                  ; universal time of the first completed handshake
  (queries 0)                           ; queries sent (SEND-QUERY)
  (answers 0)                           ; adnl.message.answer received
  (pongs 0)                             ; tcp.pong received
  (first-rx-at nil)                     ; universal time of the first answer/pong AFTER the ack
  (events '())                          ; newest first, at most *ADNL-EVENT-LIMIT* (time . text)
  log-fn)                               ; (control &rest args) or NIL, captured at open time

(defparameter *adnl-event-limit* 30)


(defun %client-event (client control &rest args)
  "Record one diagnostic line in CLIENT's ring and pass it to its log function."
  (let ((text (apply #'format nil control args)))
    (sb-thread:with-mutex ((adnl-ext-client-lock client))
      (push (cons (get-universal-time) text) (adnl-ext-client-events client))
      (let ((ev (adnl-ext-client-events client)))
        (when (> (length ev) *adnl-event-limit*)
          (setf (adnl-ext-client-events client) (subseq ev 0 *adnl-event-limit*)))))
    (let ((fn (or (adnl-ext-client-log-fn client) *adnl-log-function*)))
      (when fn (sb-thread:with-recursive-lock (*adnl-log-lock*)
                 (ignore-errors (funcall fn "upstream ~A: ~A" (adnl-ext-client-name client) text)))))
    text))

(defun %client-stage (client stage)
  (setf (adnl-ext-client-stage client) stage
        (adnl-ext-client-stage-since client) (get-universal-time)))

(defun adnl-failure-hint (stage condition)
  "A one-line human explanation of what a failure at STAGE most likely means."
  (let ((text (princ-to-string condition)))
    (flet ((has (&rest needles) (some (lambda (n) (search n text :test #'char-equal)) needles)))
      (case stage
        ((:idle :tcp-connecting)
         (cond ((has "refused") "TCP connection refused: nothing listens on that ip:port (stale liteserver in the global config?)")
               ((has "timed out" "timeout" "unreachable")
                "TCP connect timed out / unreachable: outbound traffic to this ip:port is blocked (firewall, no route, or the host is down)")
               ((has "resolve" "name or service") "address could not be resolved")
               (t "TCP connect failed before any ADNL traffic: check outbound connectivity to this ip:port")))
        (:tcp-connected "TCP is up but sending the init packet failed: the peer closed the connection immediately")
        (:init-sent
         (cond ((has "no handshake ack" "timeout")
                "init packet sent, no ack within 5s: the peer is silent (wrong public key for this ip:port, or a middlebox swallows ADNL traffic)")
               ((has "peer closed" "receive failed" "connection closed")
                "init packet sent, then the peer closed the connection: it rejected the handshake (the public key in the global config does not match this server)")
               (t "failed between the init packet and the handshake ack")))
        (:ack-received
         "handshake acknowledged but the session died before any answer: server dropped us after the ack")
        (:ready
         (cond ((has "silent") "session was up, then the peer stopped answering (network drop or the server went away)")
               ((has "peer closed" "receive failed" "connection closed")
                "session was up, then the peer closed it (liteserver restart, rate limit or idle drop)")
               (t "the established session failed")))
        (t "unclassified failure")))))

(defun %client-record-failure (client stage condition)
  "Count the failure and remember it as LAST-FAILURE.  The event ring / log function only get a
line when it differs (stage or text) from the previous failure: a blocked network retries every
second and must not flood the log with the same line."
  (let* ((text (princ-to-string condition))
         (hint (adnl-failure-hint stage condition))
         (repeat nil))
    (sb-thread:with-mutex ((adnl-ext-client-lock client))
      (incf (adnl-ext-client-failures client))
      (let ((prev (adnl-ext-client-last-failure client)))
        (setf repeat (and prev (eq (second prev) stage) (equal (third prev) text))))
      (setf (adnl-ext-client-last-failure client)
            (list (get-universal-time) stage text hint)))
    (unless repeat
      (%client-event client "FAILED at ~(~A~): ~A -- ~A" stage text hint))))

(defun adnl-ext-client-status (client)
  "A property list describing CLIENT right now: :name :stage :stage-since :alive
:attempts :connects :failures :queries :answers :pongs :first-ready-at :first-rx-at
:last-failure (universal-time stage message hint, or NIL) :events (oldest first)."
  (sb-thread:with-mutex ((adnl-ext-client-lock client))
    (list :name (adnl-ext-client-name client)
          :stage (adnl-ext-client-stage client)
          :stage-since (adnl-ext-client-stage-since client)
          :alive (and (adnl-ext-client-ready-p client) (not (adnl-ext-client-stop-p client)) t)
          :attempts (adnl-ext-client-attempts client)
          :connects (adnl-ext-client-connects client)
          :failures (adnl-ext-client-failures client)
          :queries (adnl-ext-client-queries client)
          :answers (adnl-ext-client-answers client)
          :pongs (adnl-ext-client-pongs client)
          :first-ready-at (adnl-ext-client-first-ready-at client)
          :first-rx-at (adnl-ext-client-first-rx-at client)
          :last-failure (adnl-ext-client-last-failure client)
          :events (reverse (adnl-ext-client-events client)))))

(defun adnl-octets-key (octets)
  (octets->hex octets))

(defun adnl-ext-client-alive-p (client)
  (and (adnl-ext-client-ready-p client) (not (adnl-ext-client-stop-p client))))

(defun %client-fail-all-pending (client reason)
  (let ((waiting '()))
    (sb-thread:with-mutex ((adnl-ext-client-lock client))
      (maphash (lambda (k p) (declare (ignore k)) (push p waiting))
               (adnl-ext-client-pending client))
      (clrhash (adnl-ext-client-pending client)))
    (dolist (p waiting)
      (setf (adnl-pending-failure p) reason)
      (sb-thread:signal-semaphore (adnl-pending-semaphore p)))))

(defun %client-dispatch (client payload)
  "One received payload.  Only answers matter; pongs just refresh liveness."
  (setf (adnl-ext-client-last-rx client) (get-internal-real-time))
  (when (plusp (length payload))
    (let ((obj (handler-case (tl-decode payload) (error () nil))))
      (when (and (or (tl-is obj "adnl.message.answer") (tl-is obj "tcp.pong"))
                 (null (adnl-ext-client-first-rx-at client)))
        (setf (adnl-ext-client-first-rx-at client) (get-universal-time))
        (%client-event client "first traffic after the handshake (~A): the session works"
                       (if (tl-is obj "tcp.pong") "tcp.pong" "answer")))
      (when (tl-is obj "tcp.pong")
        (incf (adnl-ext-client-pongs client)))
      (when (tl-is obj "adnl.message.answer")
        (incf (adnl-ext-client-answers client)))
      (when (tl-is obj "adnl.message.answer")
        (let ((pending (sb-thread:with-mutex ((adnl-ext-client-lock client))
                         (let* ((key (adnl-octets-key (tl-get obj :query-id)))
                                (p (gethash key (adnl-ext-client-pending client))))
                           (remhash key (adnl-ext-client-pending client))
                           p))))
          (when pending
            (setf (adnl-pending-answer pending) (tl-get obj :answer))
            (sb-thread:signal-semaphore (adnl-pending-semaphore pending))))))))

(defun %client-serve (client conn)
  "Read/ping loop for one live connection.  Returns (via error or normally)
when the connection should be torn down."
  (let ((next-ping (get-internal-real-time)))
    (loop until (adnl-ext-client-stop-p client)
          do (let ((now (get-internal-real-time)))
               (when (>= now next-ping)
                 (adnl-send-packet conn (tl-encode (tl-make "tcp.ping" :random-id (random (expt 2 62)))))
                 (setf next-ping (+ now (* (adnl-ext-client-ping-interval client)
                                           internal-time-units-per-second))))
               (when (> (- now (adnl-ext-client-last-rx client))
                        (* (adnl-ext-client-silence-limit client) internal-time-units-per-second))
                 (error 'adnl-closed :format-control "upstream silent for ~As"
                                     :format-arguments (list (adnl-ext-client-silence-limit client))))
               (let ((p (adnl-recv-packet conn :timeout 0.5)))
                 (unless (eq p :timeout) (%client-dispatch client p)))))))

(defun %client-set-ready (client conn value)
  (let ((was (adnl-ext-client-ready-p client)))
    (sb-thread:with-mutex ((adnl-ext-client-lock client))
      (setf (adnl-ext-client-conn client) (and value conn)
            (adnl-ext-client-ready-p client) value))
    (cond ((and value (not was) (adnl-ext-client-on-ready client))
           (ignore-errors (funcall (adnl-ext-client-on-ready client) client)))
          ((and (not value) was (adnl-ext-client-on-not-ready client))
           (ignore-errors (funcall (adnl-ext-client-on-not-ready client) client))))))

(defun %client-loop (client)
  (loop until (adnl-ext-client-stop-p client)
        do (let ((conn nil) (reached-ready nil))
             (handler-case
                 (progn
                   (incf (adnl-ext-client-attempts client))
                   (%client-stage client :tcp-connecting)
                   (when (= 1 (adnl-ext-client-attempts client))
                     (%client-event client "connecting to ~A:~D" (adnl-ext-client-host client)
                                    (adnl-ext-client-port client)))
                   (setf conn (adnl-connect (adnl-ext-client-host client) (adnl-ext-client-port client)
                                            (adnl-ext-client-server-public client)
                                            :on-stage (lambda (st) (%client-stage client st))))
                   ;; The server's implicit ack (an empty packet) arrives first.
                   (let ((ack (adnl-recv-packet conn :timeout 5)))
                     (when (eq ack :timeout)
                       (error 'adnl-closed :format-control "no handshake ack from upstream")))
                   (%client-stage client :ack-received)
                   (setf (adnl-ext-client-last-rx client) (get-internal-real-time))
                   (incf (adnl-ext-client-connects client))
                   (setf reached-ready t)
                   (unless (adnl-ext-client-first-ready-at client)
                     (setf (adnl-ext-client-first-ready-at client) (get-universal-time)))
                   (%client-event client "handshake acknowledged (connect #~D)"
                                  (adnl-ext-client-connects client))
                   (adnl-log "upstream ~A connected" (adnl-ext-client-name client))
                   (%client-stage client :ready)
                   (%client-set-ready client conn t)
                   (%client-serve client conn))
               (error (e)
                 (setf (adnl-ext-client-last-error client) e)
                 (unless (adnl-ext-client-stop-p client)
                   ;; A session that reached :ready and then died is reported as failing
                   ;; at :ready, not wherever the loop variable happens to point.
                   (%client-record-failure client
                                           (if reached-ready :ready (adnl-ext-client-stage client))
                                           e))
                 (adnl-log "upstream ~A: ~A" (adnl-ext-client-name client) e)))
             (%client-set-ready client conn nil)
             (%client-fail-all-pending client "upstream connection lost")
             (when conn (adnl-conn-close conn))
             (unless (adnl-ext-client-stop-p client) (%client-stage client :idle))
             (loop repeat (round (* 10 (adnl-ext-client-reconnect-delay client)))
                   until (adnl-ext-client-stop-p client)
                   do (sleep 0.1)))))

(defun open-adnl-ext-client (host port server-public &key name on-ready on-not-ready
                                                        (ping-interval 10) (silence-limit 35)
                                                        (reconnect-delay 1) log)
  "Start a client thread for the liteserver at HOST:PORT whose ed25519 public key
is SERVER-PUBLIC (32 octets).  Returns at once; the thread connects (and
reconnects) in the background.  ON-READY / ON-NOT-READY are called with the
client on each transition."
  (let ((client (%make-adnl-ext-client :name (or name (format nil "~A:~D" host port))
                                       :host host :port port
                                       :server-public (coerce server-public '(simple-array (unsigned-byte 8) (*)))
                                       :on-ready on-ready :on-not-ready on-not-ready
                                       :ping-interval ping-interval :silence-limit silence-limit
                                       :reconnect-delay reconnect-delay
                                       :log-fn (or log *adnl-log-function*))))
    (setf (adnl-ext-client-thread client)
          (sb-thread:make-thread (lambda () (%client-loop client))
                                 :name (format nil "adnl-ext-client ~A" (adnl-ext-client-name client))))
    client))

(defun close-adnl-ext-client (client)
  (when client
    (setf (adnl-ext-client-stop-p client) t)
    (let ((conn (adnl-ext-client-conn client)))
      (when conn (adnl-conn-close conn)))
    (let ((th (adnl-ext-client-thread client)))
      (when (and th (not (eq th sb-thread:*current-thread*)))
        (sb-thread:join-thread th :default nil :timeout 5)))
    (%client-fail-all-pending client "client closed"))
  nil)

(defun adnl-ext-client-send-query (client payload &optional (timeout 8))
  "Send PAYLOAD (octets: the already-encoded inner query) as an
adnl.message.query and return the matching answer's payload octets, verbatim.
Signals ADNL-NOT-READY when there is no live session, ADNL-TIMEOUT when no
answer arrives within TIMEOUT seconds, ADNL-CLOSED if the session dies first."
  (let* ((conn (sb-thread:with-mutex ((adnl-ext-client-lock client))
                 (and (adnl-ext-client-ready-p client) (adnl-ext-client-conn client))))
         (query-id (tl-random-int256))
         (key (adnl-octets-key query-id))
         (pending (make-adnl-pending)))
    (unless conn
      (error 'adnl-not-ready :format-control "upstream ~A is not connected"
                             :format-arguments (list (adnl-ext-client-name client))))
    (sb-thread:with-mutex ((adnl-ext-client-lock client))
      (incf (adnl-ext-client-queries client))
      (setf (gethash key (adnl-ext-client-pending client)) pending))
    (handler-case
        (adnl-send-packet conn (tl-encode (tl-make "adnl.message.query" :query-id query-id
                                                                       :query payload)))
      (error (e)
        (sb-thread:with-mutex ((adnl-ext-client-lock client))
          (remhash key (adnl-ext-client-pending client)))
        (error 'adnl-closed :format-control "send to upstream ~A failed: ~A"
                            :format-arguments (list (adnl-ext-client-name client) e))))
    (unless (sb-thread:wait-on-semaphore (adnl-pending-semaphore pending) :timeout timeout)
      (sb-thread:with-mutex ((adnl-ext-client-lock client))
        (remhash key (adnl-ext-client-pending client)))
      (error 'adnl-timeout :format-control "upstream ~A: no answer within ~As"
                           :format-arguments (list (adnl-ext-client-name client) timeout)))
    (when (adnl-pending-failure pending)
      (error 'adnl-closed :format-control "upstream ~A: ~A"
                          :format-arguments (list (adnl-ext-client-name client)
                                                  (adnl-pending-failure pending))))
    (adnl-pending-answer pending)))
