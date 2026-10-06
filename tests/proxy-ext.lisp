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

(defvar *slowness*
  (let ((e (uiop:getenv "TON_TRADER_TEST_SLOWNESS")))
    (or (and e (plusp (length e))
             (let ((v (ignore-errors (let ((*read-eval* nil)) (read-from-string e)))))
               (and (realp v) (>= v 1) v)))
        1))
  "Multiplier for the time bounds and waits of the timing-sensitive checks.  Set the environment
variable TON_TRADER_TEST_SLOWNESS (say 3) on a slow machine or a loaded one: the suites then wait
longer for things to happen and accept proportionally slower answers.  Nothing is skipped.")

(defun %scaled (seconds) (* seconds *slowness*))

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
  (loop repeat (round (* 10 (%scaled seconds))) until (cl-ton::adnl-ext-client-alive-p client) do (sleep 0.1))
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
    (loop repeat (round (* 10 (%scaled seconds)))
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

  (setf cl-ton:*proxy-hedge-delay* 1)   ; global: the query threads do not see a LET binding
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
            (let* ((np (let ((cl-ton::*proxy-query-timeout* 4))
                         (open-proxy-liteserver :implementation :native :global-config cfg
                                                :db (format nil "~Astall/" dir))))
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
                         (check "stall: nobody waits the query timeout: the hedge (1 s) asks the healthy upstream"
                                (< secs (%scaled 25)))))
                     ;; the stalled attempt is not cancelled: it ends at the query timeout (4 s) and is then counted
                     (%diag-wait np (lambda (d) (declare (ignore d))
                                      (plusp (%outcome-count np "getAccountState" :timeout))) 10)
                     (check "stall: the silent upstream's timeouts were counted by method"
                            (plusp (%outcome-count np "getAccountState" :timeout)))
                     (check "stall: the healthy upstream's answers were counted as ok"
                            (>= (%outcome-count np "getAccountState" :ok) 6))
                     (check "stall: after a timeout the silent upstream is penalized (and its failure streak grows)"
                            (let ((u (find-if (lambda (u) (plusp (count :timeout (getf u :outcomes) :key #'second)))
                                              (getf (cl-ton:proxy-diagnostics np) :upstreams))))
                              (and u (getf u :penalized) (plusp (getf u :fail-streak)))))
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
                     (check "single upstream: a silent upstream gets the FULL query timeout (no hedging with one upstream)"
                            (>= secs 1.8))
                     (check "single upstream: answered with the released binary's 652 text"
                            (equal r '(:error 652 "Gateway error: timeout for adnl query q")))
                     (check "single upstream: exactly one attempt was made"
                            (= 1 (%outcome-count np "getAccountState" :timeout)))))
              (cl-ton::close-adnl-ext-client c)
              (close-proxy-liteserver np)
              (cl-ton::stop-adnl-ext-server only)))))))
  (setf cl-ton:*proxy-hedge-delay* 2))

;;; --- diagnostics: tonlib's connections to the proxy, answer times --------------------

(defun %server-plist (np) (getf (cl-ton:proxy-diagnostics np) :server))

(defun test-proxy-connection-stats ()
  (format t "native proxy: inbound connection lifecycle and answer-time diagnostics~%")
  (let* ((*print-pretty* nil) (dir (%tmpdir "connstats")) (seq (list 9)))
    (multiple-value-bind (up kp) (%scripted-upstream
                                  (lambda (n) (if (string= n "getBlockProof") '(:stall 2) :ok)) seq)
      (let ((cfg (format nil "~Aconn.json" dir)))
        (%write-global-config cfg (list (list (cl-ton::adnl-ext-server-port up)
                                              (cl-ton::base64-encode (keypair-public kp)))))
        (let ((np (open-proxy-liteserver :implementation :native :global-config cfg
                                         :db (format nil "~Aconn/" dir))))
          (unwind-protect
               (progn
                 (cl-ton:proxy-wait-ready np :timeout 10)
                 ;; 1. an orderly client: three queries, then it hangs up
                 (let ((c (%client-for-proxy np)))
                   (%wait-ready c)
                   (dotimes (i 3) (%ask-raw c (%account-query)))
                   (check "conn stats: the live connection is listed with its query count"
                          (let ((live (getf (getf (%diag-wait
                                                   np (lambda (d) (let ((l (getf (getf d :server) :live-conns)))
                                                                    (and l (= 3 (getf (first l) :answered)))))
                                                   4)
                                                  :server)
                                            :live-conns)))
                            (and (= 1 (length live)) (= 3 (getf (first live) :queries))
                                 (= 3 (getf (first live) :answered)))))
                   (cl-ton::close-adnl-ext-client c))
                 (let ((d (%diag-wait np (lambda (d) (plusp (getf (getf d :server) :closed-count))) 6)))
                   (let ((c1 (first (getf (getf d :server) :closed-conns))))
                     (check "conn stats: the hang-up is recorded: 3 queries, 3 answered, none late"
                            (and c1 (= 3 (getf c1 :queries)) (= 3 (getf c1 :answered))
                                 (zerop (getf c1 :late)) (getf c1 :closed) (stringp (getf c1 :reason))))))
                 ;; 2. an impatient client: asks a slow query (2 s upstream), gives up after 0.5 s
                 (let ((c (%client-for-proxy np)))
                   (%wait-ready c)
                   (let ((th (sb-thread:make-thread
                              (lambda () (%ask-raw c (%proof-query) 0.5)))))
                     (sb-thread:join-thread th :timeout 5 :default nil)
                     (cl-ton::close-adnl-ext-client c)))
                 (let ((d (%diag-wait np (lambda (d) (plusp (getf (getf d :server) :late-answers))) 8)))
                   (check "conn stats: an answer that finished after the client left is counted as late"
                          (= 1 (getf (getf d :server) :late-answers)))
                   (let ((c2 (first (getf (getf d :server) :closed-conns))))
                     (check "conn stats: that connection shows 1 query, 0 answered, 1 late"
                            (and c2 (= 1 (getf c2 :queries)) (zerop (getf c2 :answered)) (= 1 (getf c2 :late))))
                     (check "conn stats: ...and it had 1 query in flight when the client left"
                            (and c2 (= 1 (getf c2 :in-flight-at-close))))))
                 ;; 3. answer times: the stalled getBlockProof shows as slow, per upstream and as served
                 (let* ((d (cl-ton:proxy-diagnostics np))
                        (served (assoc "getBlockProof" (getf d :served) :test #'string=))
                        (u (first (getf d :upstreams)))
                        (lat (assoc "getBlockProof" (getf u :latency) :test #'string=)))
                   (check "latency: the proxy's served time for getBlockProof reflects the 2 s upstream"
                          (and served (>= (fourth served) 1.8)))
                   (check "latency: the upstream's own answer time is recorded too"
                          (and lat (>= (fourth lat) 1.8)))
                   (check "latency: account queries (instant) are fast"
                          (let ((a (assoc "getAccountState" (getf d :served) :test #'string=)))
                            (and a (< (third a) 1.0)))))
                 (let ((r (cl-ton:proxy-diagnostics-report np)))
                   (flet ((has (x) (or (search x r) (progn (format t "    (report lacks: ~A)~%~A~%" x r) nil))))
                     (check "report: shows tonlib connections, closed ones with their reason, and answer times"
                            (and (has "tonlib connections: 2 opened, 2 closed")
                                 (has "answers undeliverable because the client was already gone: 1")
                                 (has "answer time as tonlib sees it")
                                 (has "1 late, 1 in flight")
                                 (has "    answer time: ")
                                 (has "getBlockProof 1 2."))))))
            (close-proxy-liteserver np)
            (cl-ton::stop-adnl-ext-server up)))))))

;;; --- hedging, adaptive delay, escalating penalty, preference for fast upstreams, standby ---

(defun %cfg-for (dir name &rest servers)
  "Write a global config for the (SERVER . KEYPAIR) pairs in SERVERS; returns its path."
  (let ((cfg (format nil "~A~A.json" dir name)))
    (%write-global-config cfg (loop for (srv . kp) in servers
                                    collect (list (cl-ton::adnl-ext-server-port srv)
                                                  (cl-ton::base64-encode (keypair-public kp)))))
    cfg))

(defun %scripted (behaviour seqno)
  "(SERVER KEYPAIR CALLS) from %SCRIPTED-UPSTREAM as a list, so the caller can destructure it."
  (multiple-value-list (%scripted-upstream behaviour seqno)))

(defun test-proxy-hedging ()
  (format t "native proxy: hedged requests, adaptive delay, penalties, speed preference, standby~%")
  ;; --- pure: the adaptive hedge delay
  (let ((p (cl-ton::%make-lisp-proxy :keypair nil :db nil))
        (q (cl-ton::proxy-query-info (cl-ton::tl-make "liteServer.getBlockProof" :mode 1
                                                      :known-block (cl-ton::tl-block-id-ext))))
        (cl-ton:*proxy-hedge-delay* 2))
    (check "hedge delay: before enough samples it is the configured initial delay"
           (= 2 (cl-ton:proxy-hedge-delay p q nil)))
    (setf (gethash "getBlockProof" (cl-ton::lisp-proxy-method-latency p)) (cons 5 2.0))
    (check "hedge delay: follows the measured answer time (0.3 + 1.5 x 2.0 s)"
           (< (abs (- 3.3 (cl-ton:proxy-hedge-delay p q nil))) 1e-6))
    (setf (gethash "getBlockProof" (cl-ton::lisp-proxy-method-latency p)) (cons 5 0.05))
    (check "hedge delay: a fast network hedges early, but not below the minimum"
           (= cl-ton:*proxy-hedge-min* (cl-ton:proxy-hedge-delay p q nil)))
    (setf (gethash "getBlockProof" (cl-ton::lisp-proxy-method-latency p)) (cons 5 30.0))
    (check "hedge delay: a very slow network is capped at the maximum"
           (= cl-ton:*proxy-hedge-max* (cl-ton:proxy-hedge-delay p q nil)))
    (check "hedge delay: a wait request is never raced"
           (null (cl-ton:proxy-hedge-delay p q (cl-ton::tl-make "liteServer.waitMasterchainSeqno"
                                                               :seqno 1 :timeout-ms 1000)))))
  ;; --- pure: escalating penalty
  (let* ((p (cl-ton::%make-lisp-proxy :keypair nil :db nil))
         (up (cl-ton::make-proxy-upstream :name "x"))
         (q (cl-ton::proxy-query-info (cl-ton::tl-make "liteServer.getMasterchainInfo")))
         (itu internal-time-units-per-second))
    (flet ((penalty-secs () (round (/ (- (cl-ton::proxy-upstream-penalty-until up) (get-internal-real-time)) itu))))
      (cl-ton::proxy-note-failure p up)
      (let ((a (penalty-secs)))
        (cl-ton::proxy-note-failure p up)
        (let ((b (penalty-secs)))
          (cl-ton::proxy-note-failure p up)
          (let ((c (penalty-secs)))
            (check "penalty: doubles with every consecutive failure (10, 20, 40 s)"
                   (and (<= 9 a 10) (<= 19 b 20) (<= 39 c 40)))
            (dotimes (i 10) (cl-ton::proxy-note-failure p up))
            (check "penalty: capped (at 120 s)" (<= (penalty-secs) 120))
            (check "penalty: the failure streak is counted"
                   (= 13 (cl-ton::proxy-upstream-fail-streak up)))
            (cl-ton::proxy-note-success p up q 0.1)
            (check "penalty: an answer clears the streak and the penalty"
                   (and (zerop (cl-ton::proxy-upstream-fail-streak up))
                        (not (cl-ton::proxy-upstream-penalized-p up))))))))
    ;; weights
    (let ((fast (cl-ton::make-proxy-upstream :name "f" :slowness 0.25))
          (slow (cl-ton::make-proxy-upstream :name "s" :slowness 2.0))
          (flaky (cl-ton::make-proxy-upstream :name "k" :slowness 1.0 :fail-streak 3)))
      (check "weight: a fast upstream outweighs a slow one by a wide margin"
             (> (cl-ton::proxy-upstream-weight fast) (* 10 (cl-ton::proxy-upstream-weight slow))))
      (check "weight: recent failures lower it, but never to zero"
             (and (< (cl-ton::proxy-upstream-weight flaky) 0.5) (plusp (cl-ton::proxy-upstream-weight flaky))))))

  (let* ((*print-pretty* nil) (dir (%tmpdir "hedge")) (seq (list 30)))
    ;; --- both upstreams slow but VALID: nothing is killed, nothing fails
    (destructuring-bind (a kpa ca) (%scripted (lambda (n) (declare (ignore n)) '(:stall 2.5)) seq)
      (declare (ignore ca))
      (destructuring-bind (b kpb cb) (%scripted (lambda (n) (declare (ignore n)) '(:stall 2.5)) seq)
        (declare (ignore cb))
        (setf cl-ton:*proxy-hedge-delay* 1)
        (let* ((cfg (%cfg-for dir "slowboth" (cons a kpa) (cons b kpb)))
               (np (open-proxy-liteserver :implementation :native :global-config cfg
                                          :db (format nil "~Aslowboth/" dir)))
               (c (%client-for-proxy np)))
          (unwind-protect
               (progn
                 (%wait-ready c) (cl-ton:proxy-wait-ready np :timeout 10)
                 (let* ((t0 (get-internal-real-time))
                        (rs (loop repeat 4 collect (%ask-raw c (%proof-query) 12)))
                        (secs (/ (- (get-internal-real-time) t0) internal-time-units-per-second)))
                   (check "slow but valid: every query gets its answer"
                          (every (lambda (r) (eq (first r) :mc-info)) rs))
                   (check "slow but valid: no answer was turned into a timeout"
                          (zerop (%outcome-count np "getBlockProof" :timeout)))
                   (check "slow but valid: ~2.5 s per query, not a multiple of it"
                          (< secs (%scaled 16)))))
            (cl-ton::close-adnl-ext-client c) (close-proxy-liteserver np)
            (cl-ton::stop-adnl-ext-server a) (cl-ton::stop-adnl-ext-server b)))))

    ;; --- the hedge: one upstream silent, one fine -> answered after about the hedge delay
    (destructuring-bind (dead kpd cd) (%scripted (lambda (n) (declare (ignore n)) '(:stall 30)) seq)
      (declare (ignore cd))
      (destructuring-bind (ok kpo co) (%scripted (lambda (n) (declare (ignore n)) :ok) seq)
        (declare (ignore co))
        (setf cl-ton:*proxy-hedge-delay* 1)
        (let* ((cfg (%cfg-for dir "hedge" (cons dead kpd) (cons ok kpo)))
               (np (let ((cl-ton::*proxy-query-timeout* 6))
                     (open-proxy-liteserver :implementation :native :global-config cfg
                                            :db (format nil "~Ahedge/" dir))))
               (c (%client-for-proxy np)))
          (unwind-protect
               (progn
                 (%wait-ready c) (cl-ton:proxy-wait-ready np :timeout 10)
                 (let ((slowest 0))
                   ;; keep asking until the silent upstream was picked first at least once (a hedge)
                   (loop repeat 60
                         do (let ((t0 (get-internal-real-time)))
                              (%ask-raw c (%account-query) 10)
                              (setf slowest (max slowest (/ (- (get-internal-real-time) t0)
                                                            internal-time-units-per-second))))
                         until (plusp (or (cl-ton::proxy-stat-value (cl-ton::%native-of np) :hedge) 0)))
                   (check "hedge: a query that went to the silent upstream first was hedged"
                          (plusp (or (cl-ton::proxy-stat-value (cl-ton::%native-of np) :hedge) 0)))
                   (check "hedge: ... and was still answered within the hedge delay + margin, not the timeout"
                          (< slowest (%scaled 3.5)))))
            (cl-ton::close-adnl-ext-client c) (close-proxy-liteserver np)
            (cl-ton::stop-adnl-ext-server dead) (cl-ton::stop-adnl-ext-server ok)))))

    ;; --- speed preference: a fast and a slow (0.6 s) upstream, answers always valid
    (destructuring-bind (fast kpf cf) (%scripted (lambda (n) (declare (ignore n)) :ok) seq)
      (destructuring-bind (slow kps cs) (%scripted (lambda (n) (declare (ignore n)) '(:stall 0.6)) seq)
        (setf cl-ton:*proxy-hedge-delay* 5)   ; no hedging here: we measure the choice, not the race
        (let* ((cfg (%cfg-for dir "speed" (cons fast kpf) (cons slow kps)))
               (np (open-proxy-liteserver :implementation :native :global-config cfg
                                          :db (format nil "~Aspeed/" dir)))
               (c (%client-for-proxy np)))
          (unwind-protect
               (progn
                 (%wait-ready c) (cl-ton:proxy-wait-ready np :timeout 10)
                 (dotimes (i 14) (%ask-raw c (%account-query) 10))   ; learn who is fast
                 (let ((f0 (car cf)) (s0 (car cs)))
                   (dotimes (i 24) (%ask-raw c (%account-query) 10))
                   (let ((f (- (car cf) f0)) (s (- (car cs) s0)))
                     (check "speed preference: after learning, the fast upstream gets most queries"
                            (> f (* 2 s))))))
            (cl-ton::close-adnl-ext-client c) (close-proxy-liteserver np)
            (cl-ton::stop-adnl-ext-server fast) (cl-ton::stop-adnl-ext-server slow)))))
    (setf cl-ton:*proxy-hedge-delay* 2)

    ;; --- standby sessions
    (let* ((servers (loop repeat 6 collect (%scripted (lambda (n) (declare (ignore n)) :ok) seq)))
           (cfg (apply #'%cfg-for dir "standby" (mapcar (lambda (s) (cons (first s) (second s))) servers)))
           (np (let ((cl-ton:*proxy-max-active-upstreams* 2))
                 (open-proxy-liteserver :implementation :native :global-config cfg
                                        :db (format nil "~Astandby/" dir))))
           (c (%client-for-proxy np)))
      (unwind-protect
           (progn
             (%wait-ready c)
             (cl-ton:proxy-wait-ready np :timeout 10)
             (let* ((d (cl-ton:proxy-diagnostics np)) (ups (getf d :upstreams)))
               (check "standby: only MAX-ACTIVE sessions are open, the rest stand by"
                      (and (= 2 (count-if-not (lambda (u) (getf u :standby)) ups))
                           (= 4 (count-if (lambda (u) (getf u :standby)) ups))))
               (check "standby: the report counts them"
                      (search "standby 4" (cl-ton:proxy-diagnostics-report np)))
               (check "standby: the verdict looks at the active ones only"
                      (eq :ok (getf d :verdict)))
               (check "standby: queries are answered by the active ones"
                      (eq :mc-info (first (%ask-raw c (%account-query) 8)))))
             (flet ((active-servers ()
                      (let ((names (mapcar (lambda (u) (getf u :name))
                                           (remove-if (lambda (u) (getf u :standby))
                                                      (getf (cl-ton:proxy-diagnostics np) :upstreams)))))
                        (remove-if-not (lambda (s) (member (format nil "127.0.0.1:~D" (cl-ton::adnl-ext-server-port (first s)))
                                                           names :test #'string=))
                                       servers)))
                    (alive-active ()
                      (count-if (lambda (u) (and (getf u :alive) (not (getf u :standby))))
                                (getf (cl-ton:proxy-diagnostics np) :upstreams))))
               ;; one active upstream's server stops: the supervisor opens a standby in its place
               (let ((act (active-servers)))
                 (check "standby: (setup) two servers are the active ones" (= 2 (length act)))
                 (cl-ton::stop-adnl-ext-server (first (first act)))
                 (%diag-wait np (lambda (d) (declare (ignore d)) (and (= 3 (length (active-servers))) (>= (alive-active) 2))) 20)
                 (check "standby: when an active session dies a standby is opened in its place"
                        (and (= 3 (length (active-servers))) (>= (alive-active) 2))))
               ;; every active server stops at once: the next query wakes the standbys itself
               (dolist (s (active-servers)) (ignore-errors (cl-ton::stop-adnl-ext-server (first s))))
               (sleep 1.5)
               (check "standby: with every active session gone a query is still answered, by a standby"
                      (eq :mc-info (first (%ask-raw c (%account-query) 12))))))
        (cl-ton::close-adnl-ext-client c) (close-proxy-liteserver np)
        (dolist (s servers) (ignore-errors (cl-ton::stop-adnl-ext-server (first s))))))))


;;; --- weak-network resilience: patient sync, keystores, network summary, naming ------------

(defmacro %with-fake-sync ((script) &body body)
  "Run BODY with TONLIB-CALL replaced by (funcall SCRIPT): the sync request answers {\"seqno\":42}
or signals whatever SCRIPT signals."
  `(progn
     (sb-int:encapsulate 'cl-ton::tonlib-call 'fake-sync
                         (lambda (f &rest args) (declare (ignore f args)) (funcall ,script)))
     (unwind-protect (progn ,@body)
       (sb-int:unencapsulate 'cl-ton::tonlib-call 'fake-sync))))

(defun %lite-timeout () (make-condition 'cl-ton::tonlib-error :code 500 :message "LITE_SERVER_TIMEOUT: x"))

(defun test-patient-sync ()
  (format t "tonlib sync: patient while verified steps keep arriving~%")
  (let ((cl-ton:*tonlib-sync-retry-delay* 0.01))
    ;; progress grows with every failed attempt: far more attempts than the old fixed 8
    (let ((calls 0) (progress 0) (log '()))
      (%with-fake-sync ((lambda ()
                          (incf calls)
                          (if (< calls 12)
                              (progn (incf progress 10) (error (%lite-timeout)))
                              (cl-ton::json-decode "{\"seqno\":42}"))))
        (let ((r (cl-ton:tonlib-sync nil :progress (lambda () progress)
                                         :on-attempt (lambda (n e gained now) (declare (ignore e))
                                                       (push (list n gained now) log)))))
          (check "patient: 11 failed attempts that each verified steps, then success" (and (eql r 42) (= calls 12)))
          (check "patient: ON-ATTEMPT saw the steps gained each time"
                 (and (= 11 (length log)) (every (lambda (l) (= 10 (second l))) log))))))
    ;; no progress at all: gives up after 3 stalled attempts
    (let ((calls 0))
      (%with-fake-sync ((lambda () (incf calls) (error (%lite-timeout))))
        (check "patient: with no verified progress it stops after 3 attempts in a row"
               (and (handler-case (progn (cl-ton:tonlib-sync nil :progress (lambda () 0)) nil)
                      (cl-ton::tonlib-error () t))
                    (= calls 3)))))
    ;; progress then stall: the stall counter restarts when progress resumes
    (let ((calls 0) (progress 0))
      (%with-fake-sync ((lambda ()
                          (incf calls)
                          (cond ((member calls '(1 4)) (incf progress 5) (error (%lite-timeout)))
                                ((< calls 7) (error (%lite-timeout)))
                                (t (cl-ton::json-decode "{\"seqno\":7}")))))
        (check "patient: two stalled attempts, then progress, then two more stalled: still within the limit"
               (eql 7 (cl-ton:tonlib-sync nil :progress (lambda () progress))))))
    ;; an error retrying cannot help
    (let ((calls 0) (progress 0))
      (%with-fake-sync ((lambda () (incf calls) (incf progress)
                          (error 'cl-ton::tonlib-error :code 400 :message "bad request")))
        (check "patient: a non-retryable error is raised at once, however much progress there is"
               (and (handler-case (progn (cl-ton:tonlib-sync nil :progress (lambda () progress)) nil)
                      (cl-ton::tonlib-error () t))
                    (= calls 1)))))
    ;; total timeout
    (let ((calls 0) (progress 0))
      (%with-fake-sync ((lambda () (incf calls) (incf progress) (error (%lite-timeout))))
        (check "patient: the total timeout ends it even while progress continues"
               (and (handler-case (progn (cl-ton:tonlib-sync nil :progress (lambda () progress) :total-timeout -1) nil)
                      (cl-ton::tonlib-error () t))
                    (= calls 1)))))
    ;; without PROGRESS: the old fixed number of attempts
    (let ((calls 0))
      (%with-fake-sync ((lambda () (incf calls) (error (%lite-timeout))))
        (check "no progress function: exactly ATTEMPTS tries, as before"
               (and (handler-case (progn (cl-ton:tonlib-sync nil :attempts 2) nil)
                      (cl-ton::tonlib-error () t))
                    (= calls 2)))))))

(defun test-keystores ()
  (format t "tonlib keystores: private directories, one per client~%")
  (let* ((dir (%tmpdir "keystore")) (main (format nil "~Amain/" dir)))
    (let ((path (cl-ton:ensure-keystore main)))
      (check "keystore: created and returned as a namestring" (and (stringp path) (probe-file path)))
      (check "keystore: owner-only (mode 700)"
             (= #o700 (logand #o777 (sb-posix:stat-mode (sb-posix:stat (string-right-trim "/" path)))))))
    (let ((a (cl-ton:derived-keystore main "head-poller"))
          (b (cl-ton:derived-keystore main "scanner")))
      (check "derived keystore: one directory per client, under the main one"
             (and (search "main/head-poller/" a) (search "main/scanner/" b) (not (string= a b))
                  (probe-file a) (probe-file b)))
      (check "derived keystore: owner-only as well"
             (= #o700 (logand #o777 (sb-posix:stat-mode (sb-posix:stat (string-right-trim "/" a)))))))
    (check "keystore: :in-memory and NIL stay in memory"
           (and (eq :in-memory (cl-ton:ensure-keystore nil)) (eq :in-memory (cl-ton:ensure-keystore :in-memory))
                (eq :in-memory (cl-ton:derived-keystore nil "x")) (eq :in-memory (cl-ton:derived-keystore :in-memory "x"))))))

(defun %summary-proxy (n total max ok failed)
  "A bare proxy whose served table and one upstream's outcomes say: N getBlockProof answers taking
TOTAL seconds in all, the slowest MAX, and OK / FAILED upstream attempts."
  (let* ((p (cl-ton::%make-lisp-proxy :keypair nil :db nil))
         (client (cl-ton::open-adnl-ext-client "127.0.0.1" 1 (make-array 32 :element-type '(unsigned-byte 8)
                                                                          :initial-element 0)
                                               :start nil))
         (up (cl-ton::make-proxy-upstream :name "u" :client client)))
    (setf (cl-ton::lisp-proxy-upstreams p) (list up))
    (setf (gethash "getBlockProof" (cl-ton::lisp-proxy-served p)) (list n total max 0))
    (setf (gethash '("getBlockProof" :ok nil) (cl-ton::proxy-upstream-outcomes up)) ok)
    (when (plusp failed) (setf (gethash '("getBlockProof" :timeout nil) (cl-ton::proxy-upstream-outcomes up)) failed))
    p))

(defun test-network-summary ()
  (format t "network summary: fast / ok / slow / unknown~%")
  (check "summary: too few queries -> :unknown"
         (eq :unknown (cl-ton:proxy-network-summary (%summary-proxy 3 3.0 1.0 3 0))))
  (check "summary: quick answers, no failures -> :fast"
         (eq :fast (cl-ton:proxy-network-summary (%summary-proxy 100 10.0 0.4 100 0))))
  (check "summary: middling -> :ok"
         (eq :ok (cl-ton:proxy-network-summary (%summary-proxy 100 100.0 2.0 98 2))))
  (multiple-value-bind (k text) (cl-ton:proxy-network-summary (%summary-proxy 100 300.0 9.0 90 10))
    (check "summary: 3 s per answer -> :slow, and the text says what it means for the first sync"
           (and (eq k :slow) (search "slow network" text) (search "keystore" text))))
  (check "summary: many failed attempts -> :slow even when answers are quick"
         (eq :slow (cl-ton:proxy-network-summary (%summary-proxy 100 20.0 1.0 60 40))))
  (check "summary: it is part of the report"
         (search "slow network" (cl-ton:proxy-diagnostics-report (%summary-proxy 100 300.0 9.0 90 10)))))

(defun test-unknown-query-naming ()
  (format t "proxy: queries the schema does not know are named by constructor~%")
  (let* ((octets (coerce '(#xBD #x93 #x76 #xD9 1 2 3) '(simple-array (unsigned-byte 8) (*))))
         (fn (cl-ton::%decode-function octets)))
    (check "unknown query: decoded to (constructor . octets)" (and (consp fn) (= #xD97693BD (car fn))))
    (check "unknown query: named unknown-<constructor id> in the statistics"
           (string= "unknown-D97693BD" (cl-ton::qinfo-name (cl-ton::proxy-query-info fn))))))
