;;;; tests/proxy-ext.lisp -- Phase C/D scenarios: the Lisp ADNL-ext client and
;;;; the native proxy, against a Lisp upstream and (when present) the released
;;;; proxy-liteserver binary.  Binary legs skip cleanly without the binary.
(in-package :cl-ton/test)

(defun %free-port ()
  (let ((s (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
    (unwind-protect
         (progn (sb-bsd-sockets:socket-bind s (sb-bsd-sockets:make-inet-address "127.0.0.1") 0)
                (nth-value 1 (sb-bsd-sockets:socket-name s)))
      (sb-bsd-sockets:socket-close s))))

(defun %tmpdir (name)
  (let ((d (format nil "/tmp/cl-ton-test-~D-~A/" (sb-posix:getpid) name)))
    (uiop:delete-directory-tree (pathname d) :validate t :if-does-not-exist :ignore)
    (ensure-directories-exist d) d))

(defun %write-global-config (path entries)
  "ENTRIES: list of (port pubkey-base64), all on 127.0.0.1."
  (with-open-file (s path :direction :output :if-exists :supersede)
    (format s "{\"liteservers\":[~{~A~^,~}],\"validator\":{\"zero_state\":{\"workchain\":-1,\"shard\":-9223372036854775808,\"seqno\":0,\"root_hash\":\"F6OpKZKqvqeFp6CQmFomXNMfMj2EnaUSOXN+Mh+wVWk=\",\"file_hash\":\"XplPz01CXAps5qeSWUtxcyBfdAo5zVb1N979KLSKD24=\"}}}"
            (loop for (port key) in entries
                  collect (format nil "{\"ip\":2130706433,\"port\":~D,\"id\":{\"@type\":\"pub.ed25519\",\"key\":\"~A\"}}" port key)))))

(defun %mc-info-query ()
  (cl-ton::tl-encode (cl-ton::tl-make "liteServer.query"
                        :data (cl-ton::tl-encode (cl-ton::tl-make "liteServer.getMasterchainInfo")))))

(defun %describe (octets)
  (let ((o (handler-case (cl-ton::tl-decode octets) (error () nil))))
    (cond ((cl-ton::tl-is o "liteServer.error") (list :error (cl-ton::tl-get o :code) (cl-ton::tl-get o :message)))
          ((cl-ton::tl-is o "liteServer.masterchainInfo")
           (list :mc-info (cl-ton::tl-get (cl-ton::tl-get o :last) :seqno)))
          (t (list :other o)))))

(defun %ask (client &optional (timeout 6))
  (handler-case (%describe (cl-ton::adnl-ext-client-send-query client (%mc-info-query) timeout))
    (error (e) (list :exception (type-of e)))))

(defun %wait-ready (client &optional (seconds 8))
  (loop repeat (* 10 seconds) until (cl-ton::adnl-ext-client-alive-p client) do (sleep 0.1))
  (cl-ton::adnl-ext-client-alive-p client))

(defun %client-for-proxy (proxy)
  (multiple-value-bind (port id) (cl-ton::read-proxy-liteserver-identity proxy)
    (cl-ton::open-adnl-ext-client "127.0.0.1" port (cl-ton::base64-decode id))))

(defun %zero32 () (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))

(defun %fake-upstream (seqno-cell)
  "A Lisp ADNL-ext liteserver that answers getMasterchainInfo (seqno from the cons SEQNO-CELL)."
  (let* ((kp (cl-ton::adnl-generate-keypair))
         (srv (cl-ton::start-adnl-ext-server
               :keypair kp
               :handler (lambda (s c id q) (declare (ignore s c id))
                          (let ((fn (cl-ton::tl-decode (cl-ton::tl-get (cl-ton::tl-decode q) :data))))
                            (if (cl-ton::tl-is fn "liteServer.getMasterchainInfo")
                                (cl-ton::tl-encode
                                 (cl-ton::tl-make "liteServer.masterchainInfo"
                                   :last (cl-ton::tl-block-id-ext :seqno (car seqno-cell))
                                   :state-root-hash (%zero32)
                                   :init (cl-ton::tl-make "tonNode.zeroStateIdExt" :workchain -1
                                                          :root-hash (%zero32) :file-hash (%zero32))))
                                (cl-ton::tl-encode (cl-ton::tl-make "liteServer.error" :code 651
                                                                    :message "fake: unsupported"))))))))
    (values srv kp)))

(defun test-proxy-ext ()
  (format t "adnl-ext client + native proxy (Lisp upstream)~%")
  (let ((seq (list 5)) (dir (%tmpdir "ext")))
    (multiple-value-bind (up kp) (%fake-upstream seq)
      (let ((cfg (format nil "~Afake.json" dir)))
        (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port up)
                                              (cl-ton::base64-encode (keypair-public kp)))))
        (let* ((np (open-proxy-liteserver :implementation :native :global-config cfg
                                          :db (format nil "~Anative/" dir)))
               (c (%client-for-proxy np)))
          (unwind-protect
               (progn
                 (check "client connects to the native proxy" (%wait-ready c))
                 (sleep 1.5)
                 (check "proxy sees its upstream alive"
                        (= 1 (cl-ton::native-proxy-alive-upstream-count (cl-ton::proxy-liteserver-native np))))
                 (check "getMasterchainInfo answered through proxy from upstream"
                        (equal (%ask c) '(:mc-info 5)))
                 (setf (car seq) 9)
                 (check "a changed upstream state is visible on the next query"
                        (equal (%ask c) '(:mc-info 9)))
                 (cl-ton::adnl-ext-server-kill-connections up) (sleep 0.3)
                 (let ((r (%ask c)))
                   (check "killed upstream -> synthesized liteServer.error (never a dropped query)"
                          (and (eq (first r) :error) (search "Gateway error" (third r)))))
                 (sleep 2.5)
                 (check "upstream reconnects and answers again" (equal (%ask c) '(:mc-info 9)))
                 (cl-ton::stop-adnl-ext-server up) (sleep 0.5)
                 (check "stopped upstream -> synthesized error again"
                        (eq (first (%ask c)) :error)))
            (cl-ton::close-adnl-ext-client c)
            (close-proxy-liteserver np)
            (cl-ton::stop-adnl-ext-server up)))))))

(defun test-proxy-ext-vs-binary ()
  (format t "adnl-ext client / native proxy vs the released proxy-liteserver binary~%")
  (let ((bin (find-proxy-liteserver-binary)))
    (if (not bin)
        (format t "  skip no released proxy-liteserver binary found~%")
        (let* ((dir (%tmpdir "bin"))
               (dead (format nil "~Adead.json" dir)))
          (%write-global-config dead '((9 "sU7QavX2F964iI9oToP9gffQpCQIoOLppeqL/pdPvpM=")))
          (let ((bp (open-proxy-liteserver :implementation :binary :binary bin :global-config dead
                                           :db (format nil "~Abdb/" dir) :port (%free-port))))
            (unwind-protect
                 (let ((c (%client-for-proxy bp)))
                   (unwind-protect
                        (progn
                          (check "Lisp client completes the handshake with the released binary" (%wait-ready c))
                          (check "binary with no reachable upstream answers with the Gateway error"
                                 (equal (%ask c)
                                        '(:error 0 "Gateway error: no liteserver for query [ getMasterchainInfo (-1,8000000000000000) ]"))))
                     (cl-ton::close-adnl-ext-client c)))
              ;; native proxy whose upstream IS the binary
              (multiple-value-bind (port id) (cl-ton::read-proxy-liteserver-identity bp)
                (let ((cfg (format nil "~Aviabin.json" dir)))
                  (%write-global-config cfg (list (list port id)))
                  (let* ((np (open-proxy-liteserver :implementation :native :global-config cfg
                                                    :db (format nil "~Anative/" dir)))
                         (c (%client-for-proxy np)))
                    (unwind-protect
                         (progn
                           (check "native proxy handshakes with the binary as its upstream" (%wait-ready c))
                           (sleep 1.5)
                           (check "native proxy's upstream (the binary) is alive"
                                  (= 1 (cl-ton::native-proxy-alive-upstream-count (cl-ton::proxy-liteserver-native np))))
                           (check "binary's error answer is passed through the native proxy verbatim"
                                  (equal (%ask c)
                                         '(:error 0 "Gateway error: no liteserver for query [ getMasterchainInfo (-1,8000000000000000) ]"))))
                      (cl-ton::close-adnl-ext-client c)
                      (close-proxy-liteserver np)))))
              (close-proxy-liteserver bp)))))))

;;; --- diagnostics: where does the native proxy stop? ------------------------------

(defun %diag-wait (proxy predicate &optional (seconds 12))
  "Poll PROXY-DIAGNOSTICS until PREDICATE (given the plist) is true; returns the last plist."
  (let ((d nil))
    (loop repeat (* 10 seconds)
          do (setf d (cl-ton:proxy-diagnostics proxy))
             (when (funcall predicate d) (return))
             (sleep 0.1))
    d))

(defun %first-upstream (d) (first (getf d :upstreams)))

(defun test-proxy-diagnostics ()
  (format t "proxy diagnostics: verdicts, failure stages, hints~%")
  ;; pure: PROXY-VERDICT over synthetic upstream plists
  (flet ((u (&rest kv) (append kv (list :alive nil :failures 0 :poll-state nil))))
    (check "verdict: no upstreams"
           (eq :no-upstreams (cl-ton:proxy-verdict '())))
    (check "verdict: alive + polled ok -> :ok"
           (eq :ok (cl-ton:proxy-verdict (list (list :alive t :poll-state :ok :failures 0)))))
    (check "verdict: alive but poll errors -> :connected-silent"
           (eq :connected-silent (cl-ton:proxy-verdict (list (list :alive t :poll-state :error :failures 0)))))
    (check "verdict: alive, nothing polled yet -> :connected-silent"
           (eq :connected-silent (cl-ton:proxy-verdict (list (list :alive t :poll-state nil :failures 0)))))
    (check "verdict: every upstream failed at TCP -> :tcp-unreachable"
           (eq :tcp-unreachable
               (cl-ton:proxy-verdict (list (u :failures 2 :last-failure '(0 :tcp-connecting "x" "h"))
                                           (u :failures 1 :last-failure '(0 :tcp-connecting "x" "h"))))))
    (check "verdict: TCP ok but handshake fails -> :handshake-rejected"
           (eq :handshake-rejected
               (cl-ton:proxy-verdict (list (u :failures 1 :last-failure '(0 :init-sent "x" "h"))))))
    (check "verdict: one TCP failure + one handshake failure -> :handshake-rejected"
           (eq :handshake-rejected
               (cl-ton:proxy-verdict (list (u :failures 1 :last-failure '(0 :tcp-connecting "x" "h"))
                                           (u :failures 1 :last-failure '(0 :init-sent "x" "h"))))))
    (check "verdict: nothing failed, nothing ready -> :starting"
           (eq :starting (cl-ton:proxy-verdict (list (u :attempts 1))))))
  (check "hint: refused connection says nothing listens"
         (search "nothing listens" (cl-ton:adnl-failure-hint :tcp-connecting (make-condition 'cl-ton::adnl-closed :format-control "connect to 1.2.3.4:5 failed: Connection refused"))))
  (check "hint: ack timeout names a wrong key / middlebox"
         (search "wrong public key" (cl-ton:adnl-failure-hint :init-sent (make-condition 'cl-ton::adnl-closed :format-control "no handshake ack from upstream"))))
  (check "hint: peer closing after the init packet names a rejected handshake"
         (search "rejected the handshake" (cl-ton:adnl-failure-hint :init-sent (make-condition 'cl-ton::adnl-closed :format-control "peer closed the connection"))))

  ;; ADNL-TCP-CONNECT: bounded, with texts the hints recognise
  (let ((t0 (get-internal-real-time)))
    (check "tcp connect: a non-routable address fails within the timeout (never the OS default)"
           (and (handler-case (progn (cl-ton::adnl-tcp-connect "192.0.2.1" 9 :timeout 2) nil)
                  (cl-ton::adnl-closed () t))
                (< (/ (- (get-internal-real-time) t0) internal-time-units-per-second) 6))))
  (let ((l (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
    (sb-bsd-sockets:socket-bind l (sb-bsd-sockets:make-inet-address "127.0.0.1") 0)
    (sb-bsd-sockets:socket-listen l 4)
    (let* ((port (nth-value 1 (sb-bsd-sockets:socket-name l)))
           (sock (cl-ton::adnl-tcp-connect "127.0.0.1" port :timeout 2)))
      (check "tcp connect: a listening port connects, and the socket is blocking again"
             (and sock (not (sb-bsd-sockets:non-blocking-mode sock))))
      (ignore-errors (sb-bsd-sockets:socket-close sock))
      (sb-bsd-sockets:socket-close l)
      (check "tcp connect: a closed port says 'refused'"
             (handler-case (progn (cl-ton::adnl-tcp-connect "127.0.0.1" port :timeout 2) nil)
               (cl-ton::adnl-closed (e) (search "refused" (princ-to-string e)))))))

  ;; live: a healthy upstream
  (let* ((seq (list 5)) (dir (%tmpdir "diag")) (lines '()) (lock (sb-thread:make-mutex)))
    (multiple-value-bind (up kp) (%fake-upstream seq)
      (let ((cfg (format nil "~Ahealthy.json" dir)))
        (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port up)
                                              (cl-ton::base64-encode (keypair-public kp)))))
        (let ((np (open-proxy-liteserver :implementation :native :global-config cfg
                                         :db (format nil "~Ahealthy/" dir)
                                         :log (lambda (fmt &rest args)
                                                (sb-thread:with-mutex (lock)
                                                  (push (apply #'format nil fmt args) lines))))))
          (unwind-protect
               (multiple-value-bind (ready verdict) (cl-ton:proxy-wait-ready np :timeout 12)
                 (check "healthy upstream: proxy-wait-ready -> ready, verdict :ok" (and ready (eq verdict :ok)))
                 (let* ((d (cl-ton:proxy-diagnostics np)) (u (%first-upstream d)))
                   (check "healthy: stage :ready, alive, one handshake, no failures"
                          (and (eq :ready (getf u :stage)) (getf u :alive) (= 1 (getf u :connects))
                               (zerop (getf u :failures)) (null (getf u :last-failure))))
                   (check "healthy: first traffic after the handshake was recorded"
                          (and (getf u :first-ready-at) (getf u :first-rx-at) (plusp (getf u :answers))))
                   (check "healthy: the freshness poll answered, with the upstream's masterchain seqno"
                          (and (eq :ok (getf u :poll-state)) (eql 5 (getf u :poll-detail)) (eql 5 (getf u :seqno))))
                   (check "healthy: the listener port is the proxy's own"
                          (eql (cl-ton:proxy-liteserver-port np) (getf d :listen-port))))
                 (let ((report (cl-ton:proxy-diagnostics-report np)))
                   (check "report: names the verdict, the upstream and its seqno"
                          (and (search "verdict: OK" report) (search "answering" report) (search "poll ok (5)" report)
                               (search "upstreams: 1  answering 1" report))))
                 (check "log hook: handshake ack and first answer were logged, in order"
                        (let* ((all (reverse lines))
                               (a (position-if (lambda (l) (search "handshake acknowledged" l)) all))
                               (b (position-if (lambda (l) (search "getMasterchainInfo answered" l)) all)))
                          (and a b (< a b))))
                 ;; the inbound side: a client with the WRONG key is refused and counted
                 (let ((bad (cl-ton::open-adnl-ext-client "127.0.0.1" (cl-ton:proxy-liteserver-port np)
                                                          (keypair-public (cl-ton::adnl-generate-keypair))
                                                          :name "wrong-key-client")))
                   (unwind-protect
                        (let ((d (%diag-wait np (lambda (d) (plusp (getf (getf d :server) :rejected))) 6)))
                          (check "inbound: a client with the wrong key is rejected and counted"
                                 (plusp (getf (getf d :server) :rejected)))
                          (check "inbound: the last rejected handshake is recorded and reported"
                                 (and (getf (getf d :server) :last-reject)
                                      (search "last rejected inbound handshake" (cl-ton:proxy-diagnostics-report np))))
                          (check "inbound: the rejected client's own record names the failing stage"
                                 (let ((st (loop repeat 40
                                                 for s = (cl-ton:adnl-ext-client-status bad)
                                                 until (getf s :last-failure) do (sleep 0.1)
                                                 finally (return (cl-ton:adnl-ext-client-status bad)))))
                                   (eq :init-sent (second (getf st :last-failure))))))
                     (cl-ton::close-adnl-ext-client bad)))
                 ;; the watch thread reports a ready proxy in ONE line
                 (let ((got '()))
                   (sb-thread:join-thread
                    (cl-ton:start-proxy-watch np (lambda (fmt &rest args) (push (apply #'format nil fmt args) got))
                                              :timeout 5)
                    :timeout 8)
                   (check "watch: a ready proxy is summarised in a single line"
                          (and (= 1 (length got)) (search "ready: 1/1 upstream(s) answering" (first got))
                               (not (find #\Newline (first got)))))))
            (close-proxy-liteserver np)
            (cl-ton::stop-adnl-ext-server up))))))

  ;; live: nothing listens on the upstream port -> TCP stage
  (let* ((dir (%tmpdir "diag-dead")) (cfg (format nil "~Adead.json" dir)))
    (%write-global-config cfg (list (list (%free-port) (cl-ton::base64-encode (keypair-public (cl-ton::adnl-generate-keypair))))))
    (let ((np (open-proxy-liteserver :implementation :native :global-config cfg :db (format nil "~Adead/" dir))))
      (unwind-protect
           (let* ((d (%diag-wait np (lambda (d) (plusp (getf (%first-upstream d) :failures))) 8))
                  (u (%first-upstream d)))
             (check "dead port: failure recorded at the TCP stage"
                    (eq :tcp-connecting (second (getf u :last-failure))))
             (check "dead port: the hint says nothing listens there"
                    (search "nothing listens" (fourth (getf u :last-failure))))
             (check "dead port: verdict :tcp-unreachable" (eq :tcp-unreachable (getf d :verdict)))
             (check "dead port: the report groups the failure by cause with a count"
                    (let ((r (cl-ton:proxy-diagnostics-report np)))
                      (and (search "1 x failed at tcp-connecting" r) (search "failed 1" r))))
             (check "dead port: repeated identical failures are counted but logged once"
                    (let* ((d2 (%diag-wait np (lambda (d) (>= (getf (%first-upstream d) :failures) 3)) 10))
                           (u2 (%first-upstream d2)))
                      (and (>= (getf u2 :failures) 3)
                           (= 1 (count-if (lambda (ev) (search "FAILED at tcp-connecting" (cdr ev)))
                                          (getf u2 :events))))))
             (check "dead port: VERBOSE adds counters and event lines"
                    (let ((r (cl-ton:proxy-diagnostics-report np :verbose t)))
                      (and (search "attempts" r) (search "FAILED at tcp-connecting" r))))
             (let ((got '()))
               (sb-thread:join-thread
                (cl-ton:start-proxy-watch np (lambda (fmt &rest args) (push (apply #'format nil fmt args) got))
                                          :timeout 1)
                :timeout 6)
               (check "watch: a proxy that never became ready logs the FULL report once"
                      (and (= 1 (length got)) (search "NOT ready" (first got))
                           (search "tcp-unreachable" (string-downcase (first got)))
                           (search "nothing listens" (first got))))))
        (close-proxy-liteserver np))))

  ;; live: a server that does not know our key (right ip:port, wrong public key in the config)
  (let* ((seq (list 1)) (dir (%tmpdir "diag-key")) (cfg (format nil "~Akey.json" dir)))
    (multiple-value-bind (up kp) (%fake-upstream seq)
      (declare (ignore kp))
      (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port up)
                                            (cl-ton::base64-encode (keypair-public (cl-ton::adnl-generate-keypair))))))
      (let ((np (open-proxy-liteserver :implementation :native :global-config cfg :db (format nil "~Akey/" dir))))
        (unwind-protect
             (let* ((d (%diag-wait np (lambda (d) (plusp (getf (%first-upstream d) :failures))) 8))
                    (u (%first-upstream d)))
               (check "wrong key: the failure is at the init-packet stage, TCP itself worked"
                      (eq :init-sent (second (getf u :last-failure))))
               (check "wrong key: the hint points at the public key"
                      (search "public key" (fourth (getf u :last-failure))))
               (check "wrong key: verdict :handshake-rejected" (eq :handshake-rejected (getf d :verdict)))
               (check "wrong key: the upstream side counted a rejected handshake"
                      (plusp (cl-ton::adnl-ext-server-rejected up))))
          (close-proxy-liteserver np)
          (cl-ton::stop-adnl-ext-server up)))))

  ;; live: a peer that accepts TCP and then says nothing at all (middlebox / blackhole)
  (let* ((dir (%tmpdir "diag-mute")) (cfg (format nil "~Amute.json" dir))
         (lsock (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp))
         (held '()))
    (setf (sb-bsd-sockets:sockopt-reuse-address lsock) t)
    (sb-bsd-sockets:socket-bind lsock (sb-bsd-sockets:make-inet-address "127.0.0.1") 0)
    (sb-bsd-sockets:socket-listen lsock 8)
    (let* ((port (nth-value 1 (sb-bsd-sockets:socket-name lsock)))
           (acceptor (sb-thread:make-thread
                      (lambda () (handler-case (loop (push (sb-bsd-sockets:socket-accept lsock) held))
                                   (error () nil))))))
      (%write-global-config cfg (list (list port (cl-ton::base64-encode (keypair-public (cl-ton::adnl-generate-keypair))))))
      (let ((np (open-proxy-liteserver :implementation :native :global-config cfg :db (format nil "~Amute/" dir))))
        (unwind-protect
             (let* ((d (%diag-wait np (lambda (d) (plusp (getf (%first-upstream d) :failures))) 12))
                    (u (%first-upstream d)))
               (check "mute peer: handshake ack timeout is recorded at the init-packet stage"
                      (eq :init-sent (second (getf u :last-failure))))
               (check "mute peer: the hint says the peer is silent"
                      (search "no ack within 5s" (fourth (getf u :last-failure))))
               (check "mute peer: verdict :handshake-rejected" (eq :handshake-rejected (getf d :verdict))))
          (close-proxy-liteserver np)
          (ignore-errors (sb-bsd-sockets:socket-close lsock))
          (dolist (s held) (ignore-errors (sb-bsd-sockets:socket-close s)))
          (ignore-errors (sb-thread:join-thread acceptor :default nil :timeout 2))))))

  ;; DIAGNOSE-PROXY end to end (upstream + proxy only; the tonlib leg lives in the fakechain test)
  (let* ((seq (list 7)) (dir (%tmpdir "diag-one")))
    (multiple-value-bind (up kp) (%fake-upstream seq)
      (let ((cfg (format nil "~Aone.json" dir)))
        (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port up)
                                              (cl-ton::base64-encode (keypair-public (cl-ton::adnl-generate-keypair))))))
        (multiple-value-bind (ok report) (cl-ton:diagnose-proxy cfg :timeout 3 :stream nil)
          (check "diagnose-proxy: wrong key -> not OK, RESULT line says why"
                 (and (not ok) (search "RESULT: FAILED (handshake-rejected" report)))
          (check "diagnose-proxy: the scratch database was cleaned up"
                 (null (directory (format nil "/tmp/ton-trader-diagnose-~D-*/" (sb-posix:getpid))))))
        (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port up)
                                              (cl-ton::base64-encode (keypair-public kp)))))
        (multiple-value-bind (ok report) (cl-ton:diagnose-proxy cfg :timeout 12 :stream nil)
          (check "diagnose-proxy: healthy upstream -> OK" (and ok (search "RESULT: OK (ok)" report))))
        (cl-ton::stop-adnl-ext-server up)))))


;;; --- retry on another upstream ---------------------------------------------------

(defun %query-of (fn)
  (cl-ton::tl-encode (cl-ton::tl-make "liteServer.query" :data (cl-ton::tl-encode fn))))

(defun %proof-query ()
  "A liteServer.getBlockProof (a history query)."
  (%query-of (cl-ton::tl-make "liteServer.getBlockProof" :mode 1
                              :known-block (cl-ton::tl-block-id-ext :seqno 5)
                              :target-block (cl-ton::tl-block-id-ext :seqno 99))))

(defun %account-query ()
  "A liteServer.getAccountState (NOT a history query)."
  (%query-of (cl-ton::tl-make "liteServer.getAccountState"
                              :id (cl-ton::tl-block-id-ext :seqno 5)
                              :account (cl-ton::tl-make "liteServer.accountId" :workchain -1
                                                        :id (%zero32)))))

(defun %scripted-upstream (behaviour seqno-cell)
  "A Lisp liteserver.  BEHAVIOUR is called with the function name ('getBlockProof', ...) and
returns :OK, (:STALL seconds) -- sleep, then answer --, (:ERROR code text) or :KILL (drop every
connection without answering).  Every non-masterchain-info query is answered with a masterchainInfo
carrying the seqno, which is all the tests look at.  Returns (VALUES SERVER KEYPAIR CALLS-CELL)
where CALLS-CELL is a cons whose car counts the non-poll queries received."
  (let* ((kp (cl-ton::adnl-generate-keypair)) (calls (list 0)) (lock (sb-thread:make-mutex))
         (srv nil))
    (setf srv
          (cl-ton::start-adnl-ext-server
           :keypair kp
           :handler (lambda (s c id q) (declare (ignore s c id))
                      (let* ((fn (cl-ton::tl-decode (cl-ton::tl-get (cl-ton::tl-decode q) :data)))
                             (name (subseq (cl-ton::tl-obj-name fn) (1+ (position #\. (cl-ton::tl-obj-name fn)))))
                             (b (if (string= name "getMasterchainInfo")
                                    :ok
                                    (progn (sb-thread:with-mutex (lock) (incf (car calls)))
                                           (funcall behaviour name)))))
                        (flet ((ok () (cl-ton::tl-encode
                                       (cl-ton::tl-make "liteServer.masterchainInfo"
                                         :last (cl-ton::tl-block-id-ext :seqno (car seqno-cell))
                                         :state-root-hash (%zero32)
                                         :init (cl-ton::tl-make "tonNode.zeroStateIdExt" :workchain -1
                                                                :root-hash (%zero32) :file-hash (%zero32))))))
                          (cond ((eq b :ok) (ok))
                                ((eq b :kill) (cl-ton::adnl-ext-server-kill-connections srv) nil)
                                ((eq (first b) :stall) (sleep (second b)) (ok))
                                ((eq (first b) :error)
                                 (cl-ton::tl-encode (cl-ton::tl-make "liteServer.error" :code (second b)
                                                                                         :message (third b))))
                                (t (ok))))))))
    (values srv kp calls)))

(defun %ask-raw (client query &optional (timeout 12))
  (handler-case (%describe (cl-ton::adnl-ext-client-send-query client query timeout))
    (error (e) (list :exception (type-of e)))))

(defun %outcome-count (proxy method outcome)
  "How many METHOD/OUTCOME entries every upstream of PROXY recorded in total."
  (let ((n 0))
    (dolist (u (getf (cl-ton:proxy-diagnostics proxy) :upstreams) n)
      (dolist (o (getf u :outcomes))
        (when (and (string= (first o) method) (eq (second o) outcome)) (incf n (fourth o)))))))

(defun test-proxy-retry ()
  (format t "native proxy: a failing upstream's query is retried on another one~%")
  ;; pure helpers
  (check "history queries are recognised by name, account queries are not"
         (and (cl-ton:proxy-history-query-p (cl-ton::proxy-query-info (cl-ton::tl-make "liteServer.getBlockProof" :mode 1
                                                                                      :known-block (cl-ton::tl-block-id-ext))))
              (not (cl-ton:proxy-history-query-p
                    (cl-ton::proxy-query-info (cl-ton::tl-make "liteServer.getMasterchainInfo"))))))
  (check "error texts are grouped: runs of 3+ digits collapse"
         (string= "block (-1,#) not in db 12" (cl-ton::%collapse-digits "block (-1,96883115) not in db 12")))
  (let ((table (cl-ton:proxy-method-table
                (list (list :outcomes '(("a" :ok nil 5) ("a" :timeout nil 2) ("b" :ok nil 1)))
                      (list :outcomes '(("a" :ok nil 1) ("b" :error "x" 3)))))))
    (check "method table sums outcomes over upstreams, most failures first"
           (equal table '(("b" 1 3) ("a" 6 2)))))

  (setf cl-ton:*proxy-attempt-timeout* 1)   ; global: the query threads do not see a LET binding
  (let* ((*print-pretty* nil)
         (dir (%tmpdir "retry")) (seq (list 50)))
    ;; --- one upstream stalls forever, the other is healthy
    (progn
      (multiple-value-bind (stall kp1 calls1) (%scripted-upstream (lambda (n) (declare (ignore n)) '(:stall 30)) seq)
        (multiple-value-bind (good kp2) (%scripted-upstream (lambda (n) (declare (ignore n)) :ok) seq)
          (let ((cfg (format nil "~Astall.json" dir)))
            (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port stall)
                                                  (cl-ton::base64-encode (keypair-public kp1)))
                                            (list (cl-ton::adnl-ext-server-port good)
                                                  (cl-ton::base64-encode (keypair-public kp2)))))
            (let* ((np (open-proxy-liteserver :implementation :native :global-config cfg
                                              :db (format nil "~Astall/" dir)))
                   (c (%client-for-proxy np)))
              (unwind-protect
                   (progn
                     (check "stall: both upstreams come up" (and (%wait-ready c)
                                                                (cl-ton:proxy-wait-ready np :timeout 10)
                                                                (= 2 (cl-ton::native-proxy-alive-upstream-count
                                                                      (cl-ton::proxy-liteserver-native np)))))
                     (let ((t0 (get-internal-real-time)) (results '()))
                       ;; the pick is random: keep asking until the silent upstream was picked once
                       ;; (it is penalized after that, so only that one query pays the attempt limit)
                       (loop repeat 60
                             do (push (%ask-raw c (%account-query)) results)
                             until (and (>= (length results) 6)
                                        (plusp (%outcome-count np "getAccountState" :timeout))))
                       (let ((secs (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
                         (check "stall: every query is answered (the silent upstream is retried around)"
                                (every (lambda (r) (eq (first r) :mc-info)) results))
                         (check "stall: nobody waits the full 8 s query timeout per query (1 s attempt limit, penalty after the first)"
                                (< secs 12))))
                     (check "stall: the silent upstream's timeouts were counted by method"
                            (plusp (%outcome-count np "getAccountState" :timeout)))
                     (check "stall: the healthy upstream's answers were counted as ok"
                            (>= (%outcome-count np "getAccountState" :ok) 6))
                     (check "stall: after a timeout the silent upstream is penalized, so later queries skip it"
                            (let ((u (find-if (lambda (u) (plusp (count :timeout (getf u :outcomes) :key #'second)))
                                              (getf (cl-ton:proxy-diagnostics np) :upstreams))))
                              (and u (getf u :penalized))))
                     (check "stall: the report shows the failed queries per upstream and per method"
                            (let ((r (cl-ton:proxy-diagnostics-report np)))
                              (and (search "query failures: getAccountState timeout" r)
                                   (search "queries by method (ok/failed): getAccountState" r)))))
                (cl-ton::close-adnl-ext-client c)
                (close-proxy-liteserver np)
                (cl-ton::stop-adnl-ext-server stall) (cl-ton::stop-adnl-ext-server good)
                calls1))))))

    ;; --- one upstream drops the connection mid-query, the other is healthy
    (multiple-value-bind (dying kp1) (%scripted-upstream (lambda (n) (declare (ignore n)) :kill) seq)
      (multiple-value-bind (good kp2) (%scripted-upstream (lambda (n) (declare (ignore n)) :ok) seq)
        (let ((cfg (format nil "~Adying.json" dir)))
          (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port dying)
                                                (cl-ton::base64-encode (keypair-public kp1)))
                                          (list (cl-ton::adnl-ext-server-port good)
                                                (cl-ton::base64-encode (keypair-public kp2)))))
          (let* ((np (open-proxy-liteserver :implementation :native :global-config cfg
                                            :db (format nil "~Adying/" dir)))
                 (c (%client-for-proxy np)))
            (unwind-protect
                 (progn
                   (%wait-ready c) (cl-ton:proxy-wait-ready np :timeout 10)
                   (let ((results (loop repeat 8 collect (%ask-raw c (%account-query) 8))))
                     (check "dying upstream: no query is lost to the connection drop"
                            (every (lambda (r) (eq (first r) :mc-info)) results)))
                   (check "dying upstream: the in-flight deaths were counted"
                          (or (plusp (%outcome-count np "getAccountState" :dead))
                              ;; the upstream may have been skipped before it ever got a query
                              (>= (%outcome-count np "getAccountState" :ok) 8))))
              (cl-ton::close-adnl-ext-client c)
              (close-proxy-liteserver np)
              (cl-ton::stop-adnl-ext-server dying) (cl-ton::stop-adnl-ext-server good))))))

    ;; --- a pruned upstream answers errors for history queries: those move on, account errors do not
    (multiple-value-bind (pruned kp1 calls1)
        (%scripted-upstream (lambda (n) (declare (ignore n)) '(:error 500 "cannot find block 12345678 (pruned)")) seq)
      (multiple-value-bind (full kp2 calls2) (%scripted-upstream (lambda (n) (declare (ignore n)) :ok) seq)
        (let ((cfg (format nil "~Apruned.json" dir)))
          (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port pruned)
                                                (cl-ton::base64-encode (keypair-public kp1)))
                                          (list (cl-ton::adnl-ext-server-port full)
                                                (cl-ton::base64-encode (keypair-public kp2)))))
          (let* ((np (open-proxy-liteserver :implementation :native :global-config cfg
                                            :db (format nil "~Apruned/" dir)))
                 (c (%client-for-proxy np)))
            (unwind-protect
                 (progn
                   (%wait-ready c) (cl-ton:proxy-wait-ready np :timeout 10)
                   (check "pruned: getBlockProof always gets a real answer, never the pruned server's error"
                          (every (lambda (r) (eq (first r) :mc-info))
                                 ;; the pick is random: ask until the pruned server was hit at least once
                                 (loop repeat 80
                                       collect (%ask-raw c (%proof-query))
                                       until (plusp (%outcome-count np "getBlockProof" :error)))))
                   (check "pruned: the pruned server's errors were counted with the digits collapsed"
                          (let ((hits (loop for u in (getf (cl-ton:proxy-diagnostics np) :upstreams)
                                            append (remove-if-not
                                                    (lambda (o) (and (eq (second o) :error)
                                                                     (search "cannot find block # (pruned)" (or (third o) ""))))
                                                    (getf u :outcomes)))))
                            (and hits (= 1 (length hits)))))
                   ;; account errors are answers about the account: passed through, not retried
                   (let ((before (+ (car calls1) (car calls2))) (errors 0) (asked 0))
                     (loop repeat 80
                           do (incf asked)
                              (when (eq (first (%ask-raw c (%account-query))) :error) (incf errors))
                           until (plusp errors))
                     (check "pruned: an error answer to an ACCOUNT query is passed through, not retried elsewhere"
                            (and (plusp errors)
                                 ;; one upstream call per query asked: the error was not retried
                                 (= asked (- (+ (car calls1) (car calls2)) before)))))
                   (check "pruned: when EVERY upstream errors on a history query the last error is passed on"
                          (progn
                            (cl-ton::stop-adnl-ext-server full)
                            (sleep 3)   ; the proxy notices the dead upstream
                            (let ((r (%ask-raw c (%proof-query))))
                              (and (eq (first r) :error) (search "pruned" (third r)))))))
              (cl-ton::close-adnl-ext-client c)
              (close-proxy-liteserver np)
              (cl-ton::stop-adnl-ext-server pruned) (ignore-errors (cl-ton::stop-adnl-ext-server full)))))))

    ;; --- one upstream only: behaviour is exactly the old one (parity with the released binary)
    (progn
      (multiple-value-bind (only kp) (%scripted-upstream (lambda (n) (declare (ignore n)) '(:stall 30)) seq)
        (let ((cfg (format nil "~Aonly.json" dir)) (cl-ton::*proxy-query-timeout* 2))
          (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port only)
                                                (cl-ton::base64-encode (keypair-public kp)))))
          (let* ((np (open-proxy-liteserver :implementation :native :global-config cfg
                                            :db (format nil "~Aonly/" dir)))
                 (c (%client-for-proxy np)))
            (unwind-protect
                 (progn
                   (%wait-ready c) (cl-ton:proxy-wait-ready np :timeout 10)
                   (let* ((t0 (get-internal-real-time))
                          (r (%ask-raw c (%account-query) 10))
                          (secs (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
                     (check "single upstream: a silent upstream gets the FULL query timeout, not the attempt limit"
                            (>= secs 1.8))
                     (check "single upstream: answered with the released binary's 652 text"
                            (equal r '(:error 652 "Gateway error: timeout for adnl query q")))
                     (check "single upstream: exactly one attempt was made"
                            (= 1 (%outcome-count np "getAccountState" :timeout)))))
              (cl-ton::close-adnl-ext-client c)
              (close-proxy-liteserver np)
              (cl-ton::stop-adnl-ext-server only)))))))
  (setf cl-ton:*proxy-attempt-timeout* 3))
