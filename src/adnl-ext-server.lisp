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

(defun %server-track (server conn)
  (sb-thread:with-mutex ((adnl-ext-server-lock server))
    (push conn (adnl-ext-server-connections server))))

(defun %server-untrack (server conn)
  (sb-thread:with-mutex ((adnl-ext-server-lock server))
    (setf (adnl-ext-server-connections server)
          (remove conn (adnl-ext-server-connections server)))))

(defun %server-answer (conn query-id answer)
  (when answer
    (handler-case
        (adnl-send-packet conn (tl-encode (tl-make "adnl.message.answer"
                                                   :query-id query-id :answer answer)))
      (error () (adnl-conn-close conn)))))

(defun %server-run-query (server conn query-id query in-flight-cell)
  (handler-case
      (%server-answer conn query-id
                      (funcall (adnl-ext-server-handler server) server conn query-id query))
    (error (e)
      (adnl-log "query handler failed: ~A" e)
      (%server-answer conn query-id
                      (tl-encode (tl-make "liteServer.error" :code -400
                                                             :message (format nil "internal error: ~A" e))))))
  (sb-thread:with-mutex ((adnl-ext-server-lock server))
    (decf (car in-flight-cell))))

(defun %server-connection-loop (server conn)
  (let ((in-flight (list 0)))
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
                          (if (>= (car in-flight) (adnl-ext-server-max-in-flight server))
                              (%server-answer conn query-id
                                              (tl-encode (tl-make "liteServer.error" :code -400
                                                                                     :message "too many queries in flight")))
                              (progn
                                (sb-thread:with-mutex ((adnl-ext-server-lock server))
                                  (incf (car in-flight)))
                                (sb-thread:make-thread
                                 (lambda () (%server-run-query server conn query-id query in-flight))
                                 :name "adnl-ext query")))))
                       (t nil)))))))))

(defun %server-connection (server socket)
  (let ((conn nil))
    (unwind-protect
         (handler-case
             (progn
               (setf conn (adnl-accept-handshake socket (adnl-ext-server-keypair server)))
               (sb-thread:with-mutex ((adnl-ext-server-lock server))
                 (incf (adnl-ext-server-handshakes server)))
               (%server-track server conn)
               (%server-connection-loop server conn))
           (error (e)
             (unless conn
               (sb-thread:with-mutex ((adnl-ext-server-lock server))
                 (incf (adnl-ext-server-rejected server))
                 (setf (adnl-ext-server-last-reject server)
                       (cons (get-universal-time) (princ-to-string e)))))
             (adnl-log "adnl-ext connection ended: ~A" e)))
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
