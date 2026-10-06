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

;;;; adnl-ext-server.lisp -- Phase D (transport half): the inbound ADNL-ext
;;;; listener shared by the Lisp proxy-liteserver AND the fakechain.  The same
;;;; code path answers tonlib in both roles, which is what proves it from both
;;;; sides (the fakechain is the upstream the proxy's Phase-C clients dial).
;;;;
;;;; sb-bsd-sockets listener on the configured port, one thread per accepted
;;;; socket.  Per connection:
;;;;
;;;;   1. 256B init packet; dst-short-id must equal ours (ADNL-ACCEPT-HANDSHAKE)
;;;;   2. ciphers installed with the direction split reversed; an empty packet
;;;;      goes back as the implicit ack
;;;;   3. packet loop: tcp.ping -> tcp.pong (same random id); adnl.message.query
;;;;      -> the HANDLER, on its own thread (a slow upstream must not stall the
;;;;      other queries pipelined on the same connection); anything else is
;;;;      ignored.  A bad length, a bad hash, or an undecodable frame closes the
;;;;      connection -- the stream cannot be resynchronised.
;;;;
;;;; The HANDLER is called as (funcall handler server conn query-id query) with
;;;; QUERY the inner payload octets and must return the answer octets (which
;;;; the server wraps as adnl.message.answer keyed by QUERY-ID) or NIL to send
;;;; nothing.

(in-package :cl-ton)

(defstruct (adnl-ext-server (:constructor %make-adnl-ext-server) (:copier nil))
  keypair host port socket thread handler
  (stop-p nil)
  (lock (sb-thread:make-mutex :name "adnl-ext-server"))
  (connections '())
  (max-in-flight 256)
  (handshakes 0)
  (rejected 0)
  (last-reject nil)                      ; (universal-time . text) of the latest refused handshake
  (live-stats '())                       ; ADNL-CONN-STAT of every open connection
  (closed-stats '())                     ; the latest finished ones, newest first, at most 30
  (closed-count 0)
  (late-answers 0)                       ; answers computed but undeliverable: the client was gone
  (query-log nil))                       ; when a list cell: (:log . entries), newest first

(defun adnl-ext-server-note-query (server query)
  "Record QUERY (inner octets) in the server's query log when enabled."
  (let ((cell (adnl-ext-server-query-log server)))
    (when cell
      (sb-thread:with-mutex ((adnl-ext-server-lock server))
        (push query (cdr cell))))))

(defun adnl-ext-server-enable-query-log (server)
  (setf (adnl-ext-server-query-log server) (list :log))
  server)

(defun adnl-ext-server-logged-queries (server)
  "Inner query octets received so far, oldest first."
  (sb-thread:with-mutex ((adnl-ext-server-lock server))
    (reverse (cdr (adnl-ext-server-query-log server)))))

(defstruct (adnl-conn-stat (:copier nil))
  "What happened on one inbound connection, for diagnostics (ADNL-EXT-SERVER-CONNECTION-STATS)."
  (opened (get-universal-time))
  (closed nil)
  (queries 0)
  (answered 0)
  (late 0)                              ; answers that could not be sent (client already gone)
  (slowest 0)                           ; seconds of the slowest answered query
  (in-flight-at-close 0)
  (reason nil))

(defun adnl-ext-server-connection-stats (server)
  "(VALUES LIVE CLOSED): property lists (:opened :closed :queries :answered :late :slowest
:in-flight-at-close :reason), LIVE for open connections, CLOSED newest first (at most 30)."
  (flet ((plist (st)
           (list :opened (adnl-conn-stat-opened st) :closed (adnl-conn-stat-closed st)
                 :queries (adnl-conn-stat-queries st) :answered (adnl-conn-stat-answered st)
                 :late (adnl-conn-stat-late st) :slowest (adnl-conn-stat-slowest st)
                 :in-flight-at-close (let ((c (adnl-conn-stat-in-flight-at-close st))) (if (consp c) (car c) c))
                 :reason (adnl-conn-stat-reason st))))
    (sb-thread:with-mutex ((adnl-ext-server-lock server))
      (values (mapcar #'plist (adnl-ext-server-live-stats server))
              (mapcar #'plist (adnl-ext-server-closed-stats server))))))

(defun %server-track (server conn)
  (sb-thread:with-mutex ((adnl-ext-server-lock server))
    (push conn (adnl-ext-server-connections server))))

(defun %server-untrack (server conn)
  (sb-thread:with-mutex ((adnl-ext-server-lock server))
    (setf (adnl-ext-server-connections server)
          (remove conn (adnl-ext-server-connections server)))))

(defun %server-answer (conn query-id answer)
  "Send ANSWER; returns T when it went out, NIL when there was nothing to send or the client
is gone (the connection is then closed)."
  (when answer
    (handler-case
        (progn (adnl-send-packet conn (tl-encode (tl-make "adnl.message.answer"
                                                          :query-id query-id :answer answer)))
               t)
      (error () (adnl-conn-close conn) nil))))

(defun %server-run-query (server conn query-id query in-flight-cell stat)
  (let* ((t0 (get-internal-real-time))
         (sent (handler-case
                   (%server-answer conn query-id
                                   (funcall (adnl-ext-server-handler server) server conn query-id query))
                 (error (e)
                   (adnl-log "query handler failed: ~A" e)
                   (%server-answer conn query-id
                                   (tl-encode (tl-make "liteServer.error" :code -400
                                                                          :message (format nil "internal error: ~A" e))))))))
    (let ((secs (/ (- (get-internal-real-time) t0) (float internal-time-units-per-second))))
      (sb-thread:with-mutex ((adnl-ext-server-lock server))
        (decf (car in-flight-cell))
        (cond (sent (incf (adnl-conn-stat-answered stat))
                    (setf (adnl-conn-stat-slowest stat) (max (adnl-conn-stat-slowest stat) secs)))
              ;; computed, but the client had already gone: it gave up (or dropped) first
              ((adnl-conn-closed-p conn)
               (incf (adnl-conn-stat-late stat))
               (incf (adnl-ext-server-late-answers server))))))))

(defun %server-connection-loop (server conn stat)
  (let ((in-flight (list 0)))
    (setf (adnl-conn-stat-in-flight-at-close stat) in-flight)   ; the cell; read at close
    (loop until (or (adnl-ext-server-stop-p server) (adnl-conn-closed-p conn))
          do (let ((payload (adnl-recv-packet conn :timeout 1)))
               (unless (eq payload :timeout)
                 (when (plusp (length payload))
                   (let ((obj (tl-decode payload)))     ; undecodable => error => close
                     (cond
                       ((tl-is obj "tcp.ping")
                        (adnl-send-packet conn (tl-encode (tl-make "tcp.pong"
                                                                   :random-id (tl-get obj :random-id)))))
                       ;; The released proxy-liteserver opens every upstream with
                       ;; tcp.authentificate and treats it as unusable until it is
                       ;; answered with tcp.authentificationNonce (client nonce + 32
                       ;; random octets).  The follow-up authentificationComplete is
                       ;; accepted without checking the signature (test double).
                       ((tl-is obj "tcp.authentificate")
                        (adnl-send-packet
                         conn (tl-encode (tl-make "tcp.authentificationNonce"
                                                  :nonce (concat-octets
                                                          (list (tl-get obj :nonce)
                                                                (ironclad:random-data 32)))))))
                       ((tl-is obj "tcp.authentificationComplete") nil)
                       ((tl-is obj "adnl.message.query")
                        (let ((query-id (tl-get obj :query-id))
                              (query (tl-get obj :query)))
                          (adnl-ext-server-note-query server query)
                          (sb-thread:with-mutex ((adnl-ext-server-lock server))
                            (incf (adnl-conn-stat-queries stat)))
                          (if (>= (car in-flight) (adnl-ext-server-max-in-flight server))
                              (%server-answer conn query-id
                                              (tl-encode (tl-make "liteServer.error" :code -400
                                                                                     :message "too many queries in flight")))
                              (progn
                                (sb-thread:with-mutex ((adnl-ext-server-lock server))
                                  (incf (car in-flight)))
                                (sb-thread:make-thread
                                 (lambda () (%server-run-query server conn query-id query in-flight stat))
                                 :name "adnl-ext query")))))
                       (t nil)))))))))

(defun %server-connection (server socket)
  (let ((conn nil) (stat (make-adnl-conn-stat)) (reason "closed by the server"))
    (unwind-protect
         (handler-case
             (progn
               (setf conn (adnl-accept-handshake socket (adnl-ext-server-keypair server)))
               (sb-thread:with-mutex ((adnl-ext-server-lock server))
                 (incf (adnl-ext-server-handshakes server))
                 (push stat (adnl-ext-server-live-stats server)))
               (%server-track server conn)
               (%server-connection-loop server conn stat)
               (when (adnl-ext-server-stop-p server) (setf reason "proxy shutting down")))
           (error (e)
             (setf reason (remove #\Newline (princ-to-string e)))
             (unless conn
               (sb-thread:with-mutex ((adnl-ext-server-lock server))
                 (incf (adnl-ext-server-rejected server))
                 (setf (adnl-ext-server-last-reject server)
                       (cons (get-universal-time) (princ-to-string e)))))
             (adnl-log "adnl-ext connection ended: ~A" e)))
      (when conn
        (sb-thread:with-mutex ((adnl-ext-server-lock server))
          (let ((cell (adnl-conn-stat-in-flight-at-close stat)))
            (setf (adnl-conn-stat-in-flight-at-close stat) (if (consp cell) (car cell) 0)))
          (setf (adnl-conn-stat-closed stat) (get-universal-time)
                (adnl-conn-stat-reason stat) reason
                (adnl-ext-server-live-stats server) (remove stat (adnl-ext-server-live-stats server)))
          (incf (adnl-ext-server-closed-count server))
          (push stat (adnl-ext-server-closed-stats server))
          (when (> (length (adnl-ext-server-closed-stats server)) 30)
            (setf (adnl-ext-server-closed-stats server)
                  (subseq (adnl-ext-server-closed-stats server) 0 30)))))
      (if conn
          (progn (%server-untrack server conn) (adnl-conn-close conn))
          (ignore-errors (sb-bsd-sockets:socket-close socket))))))

(defun %server-accept-loop (server)
  (loop until (adnl-ext-server-stop-p server)
        do (handler-case
               (let ((client (sb-bsd-sockets:socket-accept (adnl-ext-server-socket server))))
                 (ignore-errors (setf (sb-bsd-sockets:sockopt-tcp-nodelay client) t))
                 (sb-thread:make-thread (lambda () (%server-connection server client))
                                        :name "adnl-ext connection"))
             (error (e)
               (unless (adnl-ext-server-stop-p server)
                 (adnl-log "accept failed: ~A" e)
                 (sleep 0.05))))))

(defun start-adnl-ext-server (&key keypair (host "127.0.0.1") (port 0) handler)
  "Listen on HOST:PORT (0 = pick a free port; read it back with
ADNL-EXT-SERVER-PORT) as the ADNL peer identified by KEYPAIR."
  (let ((socket (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
    (setf (sb-bsd-sockets:sockopt-reuse-address socket) t)
    (handler-case
        (progn
          (sb-bsd-sockets:socket-bind socket (sb-bsd-sockets:make-inet-address host) port)
          (sb-bsd-sockets:socket-listen socket 128))
      (error (e)
        (ignore-errors (sb-bsd-sockets:socket-close socket))
        (ton-error "could not listen on ~A:~D: ~A" host port e)))
    (let ((server (%make-adnl-ext-server
                   :keypair keypair :host host :socket socket :handler handler
                   :port (nth-value 1 (sb-bsd-sockets:socket-name socket)))))
      (setf (adnl-ext-server-thread server)
            (sb-thread:make-thread (lambda () (%server-accept-loop server))
                                   :name (format nil "adnl-ext listener :~D" (adnl-ext-server-port server))))
      server)))

(defun stop-adnl-ext-server (server)
  (when server
    (setf (adnl-ext-server-stop-p server) t)
    (ignore-errors (sb-bsd-sockets:socket-close (adnl-ext-server-socket server)))
    (dolist (c (sb-thread:with-mutex ((adnl-ext-server-lock server))
                 (copy-list (adnl-ext-server-connections server))))
      (adnl-conn-close c))
    (let ((th (adnl-ext-server-thread server)))
      (when (and th (not (eq th sb-thread:*current-thread*)))
        ;; accept() may sit blocked on a closed fd; poke it with a throwaway connect
        (ignore-errors
         (let ((s (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
           (sb-bsd-sockets:socket-connect s (sb-bsd-sockets:make-inet-address (adnl-ext-server-host server))
                                          (adnl-ext-server-port server))
           (sb-bsd-sockets:socket-close s)))
        (sb-thread:join-thread th :default nil :timeout 3))))
  nil)

(defun adnl-ext-server-kill-connections (server)
  "Drop every live client connection but keep listening (fault injection)."
  (dolist (c (sb-thread:with-mutex ((adnl-ext-server-lock server))
               (copy-list (adnl-ext-server-connections server))))
    (adnl-conn-close c)))
