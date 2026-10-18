;;;; tests/scenarios.lisp -- Phase F.1-F.3: real tonlib <-> (native proxy | released
;;;; proxy binary) <-> emulator-backed fakechain scenarios, plus the fakechain's own
;;;; fault-injection tests.  Everything is loopback; nothing touches a real network.
;;;;
;;;; Binary legs (A/B parity, F.2) skip cleanly when no released proxy-liteserver is
;;;; found (SKIP-MISSING); emulator/tonlib legs need the two native libraries, which a
;;;; checkout keeps in cl-ton/lib/ and a deployed build in <bin>/lib/.
(in-package :cl-ton/test)

;;; --- native libraries ---------------------------------------------------------

(defun %lib-dirs ()
  (remove nil
          (list (let ((e (uiop:getenv "TON_TRADER_LIB_DIR")))
                  (and e (plusp (length e)) (uiop:ensure-directory-pathname e)))
                (and (find-package :deploy)
                     (funcall (find-symbol "DEPLOYED-P" :deploy))
                     (merge-pathnames "lib/" (funcall (find-symbol "RUNTIME-DIRECTORY" :deploy))))
                (ignore-errors (merge-pathnames "lib/" (asdf:system-source-directory "cl-ton")))
                ;; the test-only libraries: tonlibjson (the JSON tonlib oracle) and compat/
                (ignore-errors (merge-pathnames "tests/lib/" (asdf:system-source-directory "cl-ton"))))))

(defun %lib (name)
  "Namestring of the native library NAME (e.g. \"tonlibjson-linux-x86_64.so\"), or NIL."
  (loop for d in (%lib-dirs)
        for p = (probe-file (merge-pathnames name d))
        when p return (namestring p)))

(defun %libs-available-p ()
  "True once both libraries are located and loaded."
  (let ((tl (%lib "tonlibjson-linux-x86_64.so"))
        (em (%lib "libemulator-linux-x86_64.so")))
    (when (and tl em)
      (cl-ton::load-tonlib-library tl)
      (cl-ton::load-emulator-library em)
      t)))

;;; --- helpers ------------------------------------------------------------------

(defun %until (pred &key (seconds 20) each)
  (let ((end (+ (get-internal-real-time) (* seconds internal-time-units-per-second))))
    (loop (when (funcall pred) (return t))
          (when (> (get-internal-real-time) end) (return nil))
          (when each (funcall each))
          (sleep 0.25))))

(defun %fc-client (fc)
  (cl-ton::open-adnl-ext-client "127.0.0.1" (cl-ton::fakechain-port fc)
                                (cl-ton::keypair-public (cl-ton::fakechain-keypair fc))))

(defun %fc-enqueue (fc cell)
  "Queue CELL as an accepted external/internal message (what liteServer.sendMessage does)."
  (cl-ton::with-fc-lock (fc)
    (setf (cl-ton::fakechain-queue fc) (append (cl-ton::fakechain-queue fc) (list cell)))))

(defun %fc-log-count (fc kind &optional pred)
  (count-if (lambda (e) (and (eq (first e) kind) (or (null pred) (funcall pred e))))
            (cl-ton::with-fc-lock (fc) (copy-list (cl-ton::fakechain-log fc)))))

(defparameter *scenario-keypair*
  (seed->keypair (make-array 32 :element-type '(unsigned-byte 8) :initial-element 11)))

(defun %seed-wallet (fc &key (balance (nano 10)))
  (let ((w (make-wallet-v5r1 *scenario-keypair*)))
    (cl-ton::fakechain-set-account fc (wallet-address w) :state-init (wallet-state-init w) :balance balance)
    w))

(defun %transfer (wallet seqno to value &key (bounce nil))
  (wallet-external-message
   wallet :seqno seqno
          :messages (list (make-message-spec :to to :value value :bounce bounce
                                             :body (end-cell (begin-cell))))))

(defun call-with-fc-session (fn &key (via :direct) (blocks 1) (name "sess"))
  "Start a fakechain, advance BLOCKS blocks, write its global config and open tonlib on
it: VIA :DIRECT (tonlib -> fakechain), :NATIVE (tonlib -> Lisp proxy -> fakechain) or
:BINARY (tonlib -> released proxy -> fakechain).  FN gets (FC TONLIB PROXY CONFIG)."
  (let* ((fc (cl-ton::start-fakechain))
         (dir (%tmpdir name))
         (cfg (format nil "~Afc.json" dir))
         (lib (%lib "tonlibjson-linux-x86_64.so"))
         proxy tl)
    (unwind-protect
         (progn
           (cl-ton::fakechain-advance fc blocks)
           (cl-ton::fakechain-write-global-config fc cfg)
           (ecase via
             (:direct (setf tl (cl-ton::open-tonlib cfg :library-path lib)))
             ((:native :binary)
              (setf proxy (cl-ton::open-proxy-liteserver
                           :implementation via
                           :binary (and (eq via :binary) (find-proxy-liteserver-binary))
                           :global-config cfg :db (format nil "~Aproxy/" dir)
                           :port (if (eq via :binary) (%free-port) 0)))
              (setf tl (cl-ton::open-tonlib-via-proxy proxy cfg :library-path lib))))
           (funcall fn fc tl proxy cfg))
      (ignore-errors (when tl (cl-ton::close-tonlib tl)))
      (ignore-errors (when proxy (cl-ton::close-proxy-liteserver proxy)))
      (cl-ton::stop-fakechain fc)
      (ignore-errors (uiop:delete-directory-tree (pathname dir) :validate t :if-does-not-exist :ignore)))))

(defun %seqno-via (tl fc wallet)
  "The wallet's seqno getter result through tonlib, publishing a block per retry."
  (declare (ignore fc))
  (handler-case (first (cl-ton::tonlib-run-get-method tl (wallet-address wallet) "seqno"))
    (error () nil)))

;;; --- the core scenario: runs identically over every route -----------------------

(defun %scenario-tonlib-roundtrip (via)
  "getMasterchainInfo, runSmcMethod, getAccountState, sendMessage, getTransactions and
block transactions, all through VIA; every answer is compared with what the fakechain's
emulator computed."
  (let ((label (string-downcase (symbol-name via))))
    (call-with-fc-session
     (lambda (fc tl proxy cfg)
       (declare (ignore cfg))
       (let* ((w (%seed-wallet fc))
              (dest (fake-address #x66)))
         (cl-ton::fakechain-advance fc 1)
         (check (format nil "[~A] getMasterchainInfo: tonlib sees the fakechain head" label)
                (%until (lambda () (eql (cl-ton::tonlib-masterchain-info tl) (cl-ton::fc-head-seqno fc)))
                        :seconds 15 :each (lambda () nil)))
         (check (format nil "[~A] runSmcMethod get_seqno = 0 on the seeded wallet" label)
                (%until (lambda () (eql 0 (%seqno-via tl fc w))) :seconds 15))
         (check (format nil "[~A] getAccountState balance equals the fakechain's own" label)
                (= (cl-ton::account-state-balance (cl-ton::tonlib-account-state tl (wallet-address w)))
                   (cl-ton::fakechain-account-balance fc (wallet-address w))))
         (check (format nil "[~A] sendMessage answers with a message hash" label)
                (stringp (cl-ton::tonlib-send-message tl (%transfer w 0 dest (nano 1/2)))))
         (check (format nil "[~A] emulated external advances get_seqno to 1" label)
                (%until (lambda () (eql 1 (%seqno-via tl fc w))) :seconds 30
                        :each (lambda () (cl-ton::fakechain-advance fc 1))))
         (check (format nil "[~A] the wallet balance dropped by the emulated transfer + fees" label)
                (< (cl-ton::fakechain-account-balance fc (wallet-address w)) (- (nano 10) (nano 1/2))))
         (check (format nil "[~A] getTransactions reflects the emulated transaction" label)
                (%until (lambda () (plusp (length (cl-ton::tonlib-transactions tl (wallet-address w)))))
                        :seconds 15))
         (when proxy
           (check (format nil "[~A] every tonlib query went through the proxy (fakechain saw queries)" label)
                  (plusp (%fc-log-count fc :query))))
         (when (and proxy (cl-ton::proxy-liteserver-native proxy))
           (check (format nil "[~A] native proxy counted the forwarded queries" label)
                  (plusp (cl-ton::proxy-stat-value (cl-ton::proxy-liteserver-native proxy) :queries)))))))
    :via via :name (format nil "rt-~A" label)))

;;; --- test-fakechain*: the fakechain itself -------------------------------------

(defun test-fakechain ()
  (format t "fakechain: real tonlib <-> emulator-backed liteserver (direct)~%")
  (if (not (%libs-available-p))
      (skip-missing "fakechain tonlib round trip (tonlib/libemulator shared libraries)")
      (%scenario-tonlib-roundtrip :direct)))

(defun test-fakechain-fixtures ()
  (format t "fakechain: capture/replay account fixtures~%")
  (if (not (%libs-available-p))
      (skip-missing "fakechain fixtures (libemulator)")
      (let* ((w (make-wallet-v5r1 *scenario-keypair*))
             (addr (wallet-address w))
             (si (wallet-state-init w))
             (st (cl-ton::make-account-state :address addr :balance (nano 3) :status :active
                                            :code (wallet-v5r1-code)
                                            :data (second (coerce (cl-ton::cell-refs si) (quote list)))))
             (path (format nil "~Afixture.json" (%tmpdir "fixture")))
             (fc (cl-ton::make-fakechain)))
        (unwind-protect
             (progn
               (cl-ton::write-account-fixture st path)
               (check "fixture file written" (probe-file path))
               (multiple-value-bind (a code data bal) (cl-ton::read-account-fixture path)
                 (check "fixture round trip: address" (address-equal a addr))
                 (check "fixture round trip: code/data cells" (and (node-equal code (wallet-v5r1-code))
                                                                   (node-equal data (second (coerce (cl-ton::cell-refs si) (quote list))))))
                 (check "fixture round trip: balance" (= bal (nano 3))))
               (cl-ton::fakechain-load-fixture fc path)
               (check "replayed fixture seeds the fakechain account at its original address"
                      (= (cl-ton::fakechain-account-balance fc addr) (nano 3)))
               (cl-ton::fakechain-load-fixture fc path :balance (nano 5))
               (check "an explicit BALANCE overrides the captured one"
                      (= (cl-ton::fakechain-account-balance fc addr) (nano 5))))
          (cl-ton::stop-fakechain fc)))))

(defun test-fakechain-internal ()
  (format t "fakechain: internal hops, bounce, StateInit deploy (emulator-produced)~%")
  (if (not (%libs-available-p))
      (skip-missing "fakechain internal messages (libemulator)")
      (let* ((fc (cl-ton::make-fakechain))
             (w (%seed-wallet fc :balance (nano 10)))
             (other (make-wallet-v5r1 (seed->keypair (make-array 32 :element-type '(unsigned-byte 8)
                                                                    :initial-element 12)))))
        (unwind-protect
             (progn
               ;; 1. StateInit deploy: the wallet pays a not-yet-existing wallet, deploying it
               (%fc-enqueue fc (wallet-external-message
                                w :seqno 0
                                  :messages (list (make-message-spec :to (wallet-address other)
                                                                     :value (nano 1) :bounce nil
                                                                     :state-init (wallet-state-init other)
                                                                     :body (end-cell (begin-cell))))))
               (cl-ton::fakechain-advance fc 3)
               (check "the destination was deployed by the internal message (balance > 0)"
                      (plusp (cl-ton::fakechain-account-balance fc (wallet-address other))))
               ;; 2. bounce: value to a never-deployed address with bounce set comes back
               (let ((before (cl-ton::fakechain-account-balance fc (wallet-address w))))
                 (%fc-enqueue fc (%transfer w 1 (fake-address #x77) (nano 1) :bounce t))
                 (cl-ton::fakechain-advance fc 4)
                 (let ((after (cl-ton::fakechain-account-balance fc (wallet-address w))))
                   (check "bounced value returned to the sender (only fees lost)"
                          (and (< after before) (> after (- before (nano 1/4))))))
                 (check "the never-deployed destination does not exist after the bounce"
                      (zerop (cl-ton::fakechain-account-balance fc (fake-address #x77))))))
          (cl-ton::stop-fakechain fc)))))

(defun test-fakechain-block-transactions ()
  (format t "fakechain: liteServer.listBlockTransactions via tonlib blocks.getTransactions~%")
  (if (not (%libs-available-p))
      (skip-missing "fakechain block transactions (tonlib/libemulator)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore proxy cfg))
         (let ((w (%seed-wallet fc)))
           (cl-ton::fakechain-advance fc 1)
           (%fc-enqueue fc (%transfer w 0 (fake-address #x66) (nano 1/4)))
           (cl-ton::fakechain-advance fc 1)
           (check "a shard block carries the emulated transaction"
                  (%until
                   (lambda ()
                     (let* ((blk (cl-ton::fc-head fc))
                            (id (list :|@type| "ton.blockIdExt" :|workchain| 0
                                      :|shard| (- (expt 2 63)) :|seqno| (cl-ton::fc-block-seqno blk)
                                      :|root_hash| (cl-ton::base64-encode (cl-ton::fc-block-sh-root blk))
                                      :|file_hash| (cl-ton::base64-encode (cl-ton::fc-block-sh-file blk)))))
                       (some (lambda (x) (declare (ignore x)) t)
                             (handler-case (cl-ton::tonlib-block-transactions tl id)
                               (error () nil)))))
                   :seconds 20 :each (lambda () (cl-ton::fakechain-advance fc 1))))))
       :via :direct :name "blocktx")))

(defun test-fakechain-query-faults ()
  (format t "fakechain: fail-next / answer-delay fault injection~%")
  (let* ((fc (cl-ton::start-fakechain))
         (c (%fc-client fc)))
    (unwind-protect
         (progn
           (cl-ton::fakechain-advance fc 2)
           (check "client connects to the fakechain" (%wait-ready c))
           (check "baseline: getMasterchainInfo answers" (eq :mc-info (first (%ask c))))
           (setf (cl-ton::fakechain-fail-next fc) 1)
           (check "fail-next: the next query gets liteServer.error 502"
                  (equal (%ask c) '(:error 502 "injected failure")))
           (check "and the one after is healthy again" (eq :mc-info (first (%ask c))))
           (setf (cl-ton::fakechain-answer-delay fc) 1.2)
           (let ((t0 (get-internal-real-time)))
             (%ask c)
             (check "answer-delay: the answer waited at least the injected delay"
                    (>= (/ (- (get-internal-real-time) t0) internal-time-units-per-second) 1.1)))
           (setf (cl-ton::fakechain-answer-delay fc) 0)
           (check "delay cleared: prompt answers again" (eq :mc-info (first (%ask c)))))
      (cl-ton::close-adnl-ext-client c)
      (cl-ton::stop-fakechain fc))))

(defun test-fakechain-faults ()
  (format t "fakechain: drop-externals / stall-p fault injection~%")
  (if (not (%libs-available-p))
      (skip-missing "fakechain faults (libemulator)")
      (let* ((fc (cl-ton::start-fakechain))
             (c (%fc-client fc))
             (w (%seed-wallet fc))
             (send (lambda (seqno)
                     (cl-ton::adnl-ext-client-send-query
                      c (cl-ton::tl-encode
                         (cl-ton::tl-make "liteServer.query"
                                          :data (cl-ton::tl-encode
                                                 (cl-ton::tl-make "liteServer.sendMessage"
                                                                  :body (serialize-boc (%transfer w seqno (fake-address #x66) (nano 1/4)))))))
                      6))))
        (unwind-protect
             (progn
               (cl-ton::fakechain-advance fc 1)
               (check "client connects" (%wait-ready c))
               (setf (cl-ton::fakechain-drop-externals fc) 1)
               (funcall send 0)
               (cl-ton::fakechain-advance fc 2)
               (check "drop-externals: the accepted-but-dropped external never executes"
                      (= (cl-ton::fakechain-account-balance fc (wallet-address w)) (nano 10)))
               (funcall send 0)
               (cl-ton::fakechain-advance fc 2)
               (check "the next external executes"
                      (< (cl-ton::fakechain-account-balance fc (wallet-address w)) (nano 10)))
               (let ((head (cl-ton::fc-head-seqno fc)))
                 (setf (cl-ton::fakechain-stall-p fc) t)
                 (cl-ton::fakechain-advance fc 3)
                 (check "stall-p: no blocks are produced" (= head (cl-ton::fc-head-seqno fc)))
                 (setf (cl-ton::fakechain-stall-p fc) nil)
                 (cl-ton::fakechain-advance fc 1)
                 (check "stall cleared: blocks resume" (> (cl-ton::fc-head-seqno fc) head))))
          (cl-ton::close-adnl-ext-client c)
          (cl-ton::stop-fakechain fc)))))

;;; --- proxy scenarios (F.2 / F.3) -------------------------------------------------

(defun %raw-connect (port)
  (let ((s (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
    (sb-bsd-sockets:socket-connect s (sb-bsd-sockets:make-inet-address "127.0.0.1") port)
    s))

(defun %socket-closed-by-peer-p (sock &optional (seconds 4))
  "True when the peer closes SOCK (EOF/reset) within SECONDS."
  (let ((stream (sb-bsd-sockets:socket-make-stream sock :input t :output t :element-type '(unsigned-byte 8)
                                                        :buffering :none)))
    (handler-case
        (let ((fd (sb-bsd-sockets:socket-file-descriptor sock)))
          (if (sb-sys:wait-until-fd-usable fd :input seconds)
              (let ((b (read-byte stream nil :eof)))
                (eq b :eof))
              nil))
      (error () t))))

(defun %plain-mc-query-with-wait (seqno timeout-ms)
  (cl-ton::tl-encode
   (cl-ton::tl-make "liteServer.query"
                    :data (cl-ton::%cat
                           (cl-ton::tl-encode (cl-ton::tl-make "liteServer.waitMasterchainSeqno"
                                                               :seqno seqno :timeout-ms timeout-ms))
                           (cl-ton::tl-encode (cl-ton::tl-make "liteServer.getMasterchainInfo"))))))

(defun %ask-raw (client payload &optional (timeout 8))
  (handler-case (%describe (cl-ton::adnl-ext-client-send-query client payload timeout))
    (error (e) (list :exception (type-of e)))))

(defun %inflight-loss-result (impl)
  "Kill the upstream connection while a query is in flight through IMPL's proxy."
  (let* ((fc (cl-ton::start-fakechain))
         (dir (%tmpdir (format nil "inflight-~(~A~)" impl)))
         (cfg (format nil "~Afc.json" dir))
         proxy client result)
    (unwind-protect
         (progn
           (cl-ton::fakechain-advance fc 2)
           (cl-ton::fakechain-write-global-config fc cfg)
           (setf proxy (cl-ton::open-proxy-liteserver
                        :implementation impl :binary (and (eq impl :binary) (find-proxy-liteserver-binary))
                        :global-config cfg :db (format nil "~Adb/" dir)
                        :port (if (eq impl :binary) (%free-port) 0))
                 client (%client-for-proxy proxy))
           (%wait-ready client)
           (sleep 2)                    ; proxy's upstream client must be up
           (setf (cl-ton::fakechain-answer-delay fc) 3)
           (let ((killer (sb-thread:make-thread
                          (lambda () (sleep 0.7)
                            (cl-ton::adnl-ext-server-kill-connections (cl-ton::fakechain-server fc))))))
             (setf result (%ask client 12))
             (sb-thread:join-thread killer :default nil))
           result)
      (when client (cl-ton::close-adnl-ext-client client))
      (when proxy (cl-ton::close-proxy-liteserver proxy))
      (cl-ton::stop-fakechain fc)
      (ignore-errors (uiop:delete-directory-tree (pathname dir) :validate t :if-does-not-exist :ignore)))))

(defun test-proxy-inflight-upstream-loss ()
  (format t "proxy: upstream killed with a query in flight (native == released binary)~%")
  (if (not (%libs-available-p))
      (skip-missing "in-flight upstream loss (libemulator for the fakechain)")
      (let ((native (%inflight-loss-result :native)))
        (check "native: in-flight loss -> synthesized liteServer.error 653 \"Gateway error: \""
               (equal native '(:error 653 "Gateway error: ")))
        (if (not (find-proxy-liteserver-binary))
            (skip-missing "in-flight upstream loss, released-binary leg (no proxy-liteserver binary)")
            (let ((binary (%inflight-loss-result :binary)))
              (check "binary: the same in-flight loss answer (A/B parity)" (equal binary native))
              (unless (equal binary native)
                (format t "       native=~S binary=~S~%" native binary)))))))

(defun %two-fakechain-proxy (heads fn)
  "Start one fakechain per entry of HEADS (blocks to advance each), a native proxy over all
of them, a Lisp client on the proxy; call FN with (CHAINS CLIENT PROXY)."
  (let* ((chains (mapcar (lambda (n) (let ((fc (cl-ton::start-fakechain))) (cl-ton::fakechain-advance fc n) fc)) heads))
         (dir (%tmpdir "wm"))
         (cfg (format nil "~Aups.json" dir))
         proxy client)
    (unwind-protect
         (progn
           (%write-global-config cfg (mapcar (lambda (fc) (list (cl-ton::fakechain-port fc)
                                                                (cl-ton::base64-encode
                                                                 (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))))
                                             chains))
           (setf proxy (cl-ton::open-proxy-liteserver :implementation :native :global-config cfg
                                                      :db (format nil "~Adb/" dir))
                 client (%client-for-proxy proxy))
           (%wait-ready client)
           (%until (lambda () (= (length chains)
                                 (cl-ton::native-proxy-alive-upstream-count (cl-ton::proxy-liteserver-native proxy))))
                   :seconds 10)
           (funcall fn chains client proxy))
      (when client (cl-ton::close-adnl-ext-client client))
      (when proxy (cl-ton::close-proxy-liteserver proxy))
      (mapc #'cl-ton::stop-fakechain chains)
      (ignore-errors (uiop:delete-directory-tree (pathname dir) :validate t :if-does-not-exist :ignore)))))

(defun test-proxy-scenarios ()
  (format t "proxy: seqno watermarking and malformed frames~%")
  (if (not (%libs-available-p))
      (skip-missing "proxy scenarios (libemulator for the fakechain)")
      (progn
        ;; --- single upstream: wait handling ------------------------------------------
        (%two-fakechain-proxy
         '(3)
         (lambda (chains client proxy)
           (declare (ignore proxy))
           (let ((fc (first chains)))
             (check "baseline answer teaches the proxy the upstream seqno"
                  (equal (%ask client) (list :mc-info (cl-ton::fc-head-seqno fc))))
             (check "wait for a seqno the upstream already has: answered at once"
                    (let ((t0 (get-internal-real-time))
                          (r (%ask-raw client (%plain-mc-query-with-wait 2 3000))))
                      (and (eq (first r) :mc-info)
                           (< (/ (- (get-internal-real-time) t0) internal-time-units-per-second) 1.5))))
             (check "...and the satisfied wait prefix was dropped before forwarding"
                    (zerop (%fc-log-count fc :wait)))
             (let ((advancer (sb-thread:make-thread (lambda () (sleep 0.8) (cl-ton::fakechain-advance fc 3)))))
               (let ((r (%ask-raw client (%plain-mc-query-with-wait 5 6000) 10)))
                 (check "wait for a future seqno: forwarded, answered once the block exists"
                        (and (eq (first r) :mc-info) (>= (second r) 5))))
               (sb-thread:join-thread advancer :default nil))
             (check "the forwarded wait kept the requested seqno and a timeout <= the client's"
                    (plusp (%fc-log-count fc :wait (lambda (e) (and (= (second e) 5) (<= (third e) 6000))))))
             (let ((r (%ask-raw client (%plain-mc-query-with-wait 999 700) 6)))
               (check "an unreachable seqno: the upstream's timeout error passes through"
                      (and (eq (first r) :error) (eql (second r) 652)))))))
        ;; --- divergent per-server seqnos ---------------------------------------------
        (%two-fakechain-proxy
         '(2 9)
         (lambda (chains client proxy)
           (declare (ignore proxy))
           (destructuring-bind (behind ahead) chains
             (dotimes (i 40) (%ask client))                ; teach both watermarks
             (dotimes (i 8) (%ask-raw client (%plain-mc-query-with-wait 6 1500)))
             (check "a wait only the leading server satisfies is never sent to the lagging one as a wait"
                    (zerop (%fc-log-count behind :wait)))
             (check "...and the leading server answered it without any wait prefix"
                    (and (zerop (%fc-log-count ahead :wait)) (plusp (%fc-log-count ahead :query)))))))
        ;; --- malformed / oversized frames --------------------------------------------
        (let* ((dir (%tmpdir "malformed"))
               (cfg (format nil "~Adead.json" dir)))
          (%write-global-config cfg '((9 "sU7QavX2F964iI9oToP9gffQpCQIoOLppeqL/pdPvpM=")))
          (let ((proxy (cl-ton::open-proxy-liteserver :implementation :native :global-config cfg
                                                      :db (format nil "~Adb/" dir))))
            (unwind-protect
                 (let ((port (cl-ton::proxy-liteserver-port proxy)))
                   (let ((s (%raw-connect port)))
                     (unwind-protect
                          (progn
                            (sb-bsd-sockets:socket-send s (ironclad:random-data 256) nil)
                            (check "a 256-byte handshake for the wrong identity is rejected (closed)"
                                   (%socket-closed-by-peer-p s)))
                       (ignore-errors (sb-bsd-sockets:socket-close s))))
                   (let ((s (%raw-connect port)))
                     (unwind-protect
                          (progn
                            (sb-bsd-sockets:socket-send s (ironclad:random-data 70000) nil)
                            (check "an oversized garbage burst is rejected (closed)"
                                   (%socket-closed-by-peer-p s)))
                       (ignore-errors (sb-bsd-sockets:socket-close s))))
                   (check "the proxy is still serving after malformed input"
                          (cl-ton::native-proxy-alive-p (cl-ton::proxy-liteserver-native proxy)))
                   (let ((c (%client-for-proxy proxy)))
                     (unwind-protect
                          (check "and a well-formed client still gets its (synthesized) answer"
                                 (and (%wait-ready c) (eq :error (first (%ask c)))))
                       (cl-ton::close-adnl-ext-client c))))
              (cl-ton::close-proxy-liteserver proxy)
              (ignore-errors (uiop:delete-directory-tree (pathname dir) :validate t :if-does-not-exist :ignore))))))))

;;; --- tonlib via proxy (F.3 / Phase E), native and released binary ---------------------

(defun test-tonlib-via-native-proxy ()
  (format t "tonlib -> NATIVE Lisp proxy -> fakechain (loopback only)~%")
  (if (not (%libs-available-p))
      (skip-missing "tonlib via native proxy (tonlib/libemulator shared libraries)")
      (progn
        (%scenario-tonlib-roundtrip :native)
        (call-with-fc-session
         (lambda (fc tl proxy cfg)
           (declare (ignore fc tl cfg))
           (let* ((routed (cl-ton::proxy-liteserver-global-config-path
                           proxy (cl-ton::proxy-liteserver-global-config proxy)
                           (format nil "~Arouted-check.json" (cl-ton::proxy-liteserver-db proxy))))
                  (parsed (cl-ton::json-decode (uiop:read-file-string routed)))
                  (servers (cl-ton::json-get parsed "liteservers")))
             (check "routed tonlib config lists exactly ONE liteserver" (= 1 (length servers)))
             (check "...on 127.0.0.1 (the proxy), nothing else"
                    (= (cl-ton::json-get (first servers) "ip") (cl-ton::ipv4-string->ip-int "127.0.0.1")))))
         :via :native :name "routed")
        ;; DIAGNOSE-PROXY with its tonlib leg, against the fakechain (what the
        ;; TON_TRADER_PROXY_DIAGNOSE=<config> mode of the binary runs)
        (let* ((fc (cl-ton::start-fakechain))
               (dir (%tmpdir "diagnose-tonlib"))
               (cfg (format nil "~Afc.json" dir)))
          (unwind-protect
               (progn
                 (cl-ton::fakechain-advance fc 3)
                 (cl-ton::fakechain-write-global-config fc cfg)
                 (multiple-value-bind (ok report)
                     (cl-ton:diagnose-proxy cfg :timeout 15 :tonlib t :stream nil
                                                :account "0:1111111111111111111111111111111111111111111111111111111111111111"
                                                :library-path (%lib "tonlibjson-linux-x86_64.so"))
                   (check "diagnose-proxy (tonlib leg): OK against the fakechain" ok)
                   (check "diagnose-proxy: the report carries the tonlib round trip's seqno"
                          (and (search "tonlib sync through the proxy: masterchain seqno" report)
                               (search "tonlib account read through the proxy" report)))
                   (check "diagnose-proxy: the report carries the upstream's stage and a RESULT line"
                          (and (search "stage ready" report) (search "RESULT: OK" report)))))
            (cl-ton::stop-fakechain fc)
            (ignore-errors (uiop:delete-directory-tree (pathname dir) :validate t :if-does-not-exist :ignore)))))))

(defun test-tonlib-via-binary-proxy ()
  (format t "tonlib -> RELEASED proxy-liteserver binary -> fakechain (A/B parity leg)~%")
  (cond ((not (%libs-available-p))
         (skip-missing "tonlib via released proxy (tonlib/libemulator shared libraries)"))
        ((not (find-proxy-liteserver-binary))
         (skip-missing "tonlib via released proxy (no proxy-liteserver binary)"))
        (t (%scenario-tonlib-roundtrip :binary))))

;;; --- a lagging liteserver (real-network failure): fail over, never poison the client ---

(defun %getTime-query ()
  (cl-ton::tl-encode (cl-ton::tl-make "liteServer.query"
                                      :data (cl-ton::tl-encode (cl-ton::tl-make "liteServer.getTime")))))

(defun test-proxy-lagging-failover ()
  (format t "proxy: an upstream answering \"block not in db\" (lagging shard client) fails over~%")
  (if (not (%libs-available-p))
      (skip-missing "lagging-upstream failover (libemulator for the fakechain)")
      (progn
        ;; one lagging + one healthy upstream
        (%two-fakechain-proxy
         '(5 5)
         (lambda (chains client proxy)
           (destructuring-bind (lagging healthy) chains
             (setf (cl-ton::fakechain-lagging-p lagging) t)
             (let ((answers (loop repeat 40 collect (%ask-raw client (%getTime-query)))))
               (check "no query was answered with the lagging server's \"not in db\" error (651)"
                      (notany (lambda (a) (and (eq (first a) :error) (eql (second a) 651))) answers))
               (check "the lagging upstream was tried (and penalized) at most once in 40 queries"
                      (<= (%fc-log-count lagging :lagging) 1))
               (check "...and the healthy upstream served the rest"
                      (>= (%fc-log-count healthy :query) 39))
               (check "the proxy counted the failover(s) it performed"
                      (= (cl-ton::proxy-stat-value (cl-ton::proxy-liteserver-native proxy) :failover)
                         (%fc-log-count lagging :lagging)))))))
        ;; only a lagging upstream: its answer is passed through unchanged (nothing to fail over to)
        (%two-fakechain-proxy
         '(5)
         (lambda (chains client proxy)
           (declare (ignore proxy))
           (setf (cl-ton::fakechain-lagging-p (first chains)) t)
           (let ((a (%ask-raw client (%getTime-query))))
             (check "a lone lagging upstream: its 651 answer reaches the client unchanged"
                    (and (eq (first a) :error) (eql (second a) 651)
                         (search "not in db" (third a))))
             (check "...and a masterchainInfo query is still answered normally by it"
                    (eq :mc-info (first (%ask client))))))))))

;;; --- stale upstreams (freshness pollers) and startup grace ----------------------------

(defun %non-poll-query-count (fc)
  "Queries the fakechain saw other than the proxy's own getMasterchainInfo freshness polls."
  (%fc-log-count fc :query (lambda (e) (not (search "getMasterchainInfo" (princ-to-string (second e)))))))

(defun test-proxy-stale-upstream ()
  (format t "proxy: freshness pollers keep clients off a stale upstream; a first query waits for one to come alive~%")
  (if (not (%libs-available-p))
      (skip-missing "stale-upstream avoidance (libemulator for the fakechain)")
      (progn
        ;; one stale (3 blocks) and one current (60 blocks) upstream
        (%two-fakechain-proxy
         '(3 60)
         (lambda (chains client proxy)
           (destructuring-bind (stale current) chains
             (check "the pollers learn both upstreams' seqnos without any client query"
                    (%until (lambda ()
                              (every (lambda (up) (plusp (cl-ton::proxy-upstream-seqno up)))
                                     (cl-ton::lisp-proxy-upstreams (cl-ton::proxy-liteserver-native proxy))))
                            :seconds 10))
             (dotimes (i 30) (%ask-raw client (%getTime-query)))
             (check "30 queries never reached the stale upstream"
                    (zerop (%non-poll-query-count stale)))
             (check "...the current one served them all"
                    (>= (%non-poll-query-count current) 30))
             (let ((r (%ask-raw client (%plain-mc-query-with-wait 200 600) 6)))
               (declare (ignore r))
               (check "a wait for a block nobody has yet is forwarded to the most advanced upstream only"
                      (and (zerop (%fc-log-count stale :wait))
                           (plusp (%fc-log-count current :wait))))))))
        ;; startup grace: ask immediately, before the proxy's upstream session is up
        (let* ((fc (cl-ton::start-fakechain))
               (dir (%tmpdir "grace"))
               (cfg (format nil "~Afc.json" dir))
               proxy client)
          (unwind-protect
               (progn
                 (cl-ton::fakechain-advance fc 4)
                 (cl-ton::fakechain-write-global-config fc cfg)
                 (setf proxy (cl-ton:open-proxy-liteserver :implementation :native :global-config cfg
                                                            :db (format nil "~Adb/" dir))
                       client (%client-for-proxy proxy))
                 (%wait-ready client)
                 (check "a query sent before any upstream is alive waits for one instead of failing"
                        (eq :mc-info (first (%ask client)))))
            (when client (cl-ton::close-adnl-ext-client client))
            (when proxy (cl-ton:close-proxy-liteserver proxy))
            (cl-ton::stop-fakechain fc)
            (ignore-errors (uiop:delete-directory-tree (pathname dir) :validate t :if-does-not-exist :ignore)))))))

;;; --- library cells (STON.fi v2 keeps its pool / LP / vault code in on-chain libraries) ----

(defparameter *router-data-lib-hashes*
  '("c00836440d084e44fb94316132ac5a21417ef4f429ee09b5560b5678b334c3e8"
    "a9338ecd624ca15d37e4a8d9bf677ddc9b84f0e98f05f2fb84c7afe332a281b4"
    "c95a2ed22ab516f77f9d4898dc4578e72f18a2448e8f6832334b0b4bf501bc79"
    "e874ac89ab826bb4403e5e7bdb8b95df3698d2e7187fa366246e98ce329ea613")
  "The four library references in the STON.fi v2.2 router's data cell, as shown by tonviewer
(each leaf there is x{02<hash>}: tag 2 = library reference).")

(defun %lib-ref-cell (hex)
  (cl-ton::make-cell :bits (logior (ash 2 256) (parse-integer hex :radix 16))
                     :bit-length 264 :exotic t))

(defun %router-data-cell ()
  "The cell tree of the STON.fi v2.2 router's data as tonviewer prints it."
  (let ((empty (cl-ton::make-cell)))
    (cl-ton::make-cell
     :bits (parse-integer "400408FFF62629A27C91C5080DBABAE7E2DED4352D1A41EB5E1D8ED4F87F85FD74F" :radix 16)
     :bit-length 268                    ; 67 hex digits
     :refs (list (cl-ton::make-cell :bits 0 :bit-length 194 :refs (list empty empty))
                 (cl-ton::make-cell :bits #x74FC2 :bit-length 64
                                    :refs (mapcar #'%lib-ref-cell *router-data-lib-hashes*))
                 empty))))

(defparameter *router-data-boc-hex*
  "b5ee9c720101080100e0000343400408fff62629a27c91c5080dbabae7e2ded4352d1a41eb5e1d8ed4f87f85fd74f8010203023100000000000000000000000000000000000000000000000020030304100000000000074fc2040506070000084202c00836440d084e44fb94316132ac5a21417ef4f429ee09b5560b5678b334c3e8084202a9338ecd624ca15d37e4a8d9bf677ddc9b84f0e98f05f2fb84c7afe332a281b4084202c95a2ed22ab516f77f9d4898dc4578e72f18a2448e8f6832334b0b4bf501bc79084202e874ac89ab826bb4403e5e7bdb8b95df3698d2e7187fa366246e98ce329ea613"
  "The STON.fi v2.2 router's data cell as a real BOC (copied from the explorer): the first
captured piece of real DEX contract state.")

(defun test-library-cells ()
  (format t "library cells: references found, serialized, and served by the fakechain~%")
  (let ((real (first (parse-boc (cl-ton::hex->octets *router-data-boc-hex*)))))
    (check "the real router-data BOC parses and holds the four library references, in order"
           (equal (cl-ton::collect-library-hashes real) *router-data-lib-hashes*))
    (check "the hand-built tree equals the real BOC bit for bit (same root hash)"
           (equal (cell-hash-hex real) (cell-hash-hex (%router-data-cell)))))
  (let* ((root (%router-data-cell))
         (found (cl-ton::collect-library-hashes root)))
    (check "the router data's four library references are found, once each, in order"
           (equal found *router-data-lib-hashes*))
    (check "a plain code cell has no library references"
           (null (cl-ton::collect-library-hashes (end-cell (begin-cell)))))
    (let ((again (first (parse-boc (serialize-boc root)))))
      (check "the tree survives BOC serialization with its exotic library cells intact"
             (equal (cl-ton::collect-library-hashes again) *router-data-lib-hashes*))
      (check "...and keeps its root hash" (equal (cell-hash-hex again) (cell-hash-hex root)))))
  (if (not (%libs-available-p))
      (skip-missing "fakechain libraries (tonlib/libemulator shared libraries)")
      (let* ((fc (cl-ton::start-fakechain))
             (c (%fc-client fc))
             (code (wallet-v5r1-code))
             (hex (cl-ton::fakechain-add-library fc code))
             (absent (make-string 64 :initial-element #\7)))
        (unwind-protect
             (progn
               (check "client connects to the fakechain" (%wait-ready c))
               (let* ((ask (lambda (&rest hashes)
                             (cl-ton::tl-decode
                              (cl-ton::adnl-ext-client-send-query
                               c (cl-ton::tl-encode
                                  (cl-ton::tl-make "liteServer.query"
                                                   :data (cl-ton::tl-encode
                                                          (cl-ton::tl-make "liteServer.getLibraries"
                                                                           :library-list (mapcar #'cl-ton::hex->octets hashes)))))
                               6))))
                      (r (funcall ask hex absent))
                      (entries (coerce (cl-ton::tl-get r :result) 'list)))
                 (check "liteServer.getLibraries answers libraryResult" (cl-ton::tl-is r "liteServer.libraryResult"))
                 (check "...with exactly the library the chain has (the absent one is omitted)"
                        (= 1 (length entries)))
                 (check "...whose data is that code cell"
                        (and entries
                             (equal (cell-hash-hex (first (parse-boc (cl-ton::tl-get (first entries) :data))))
                                    (cell-hash-hex code))))))
          (cl-ton::close-adnl-ext-client c)
          (cl-ton::stop-fakechain fc)))))

(defun test-fakechain-library-execution ()
  (format t "fakechain: a contract whose code is a LIBRARY CELL executes only with the library published~%")
  (if (not (%libs-available-p))
      (skip-missing "fakechain library execution (libemulator)")
      (let* ((fc (cl-ton::make-fakechain))
             (w (make-wallet-v5r1 *scenario-keypair*))
             (si (wallet-state-init w))
             (data (second (coerce (cl-ton::cell-refs si) 'list)))
             (lib-code (%lib-ref-cell (cell-hash-hex (wallet-v5r1-code)))))
        (unwind-protect
             (progn
               (cl-ton::fakechain-set-account fc (wallet-address w) :code lib-code :data data :balance (nano 10))
               (%fc-enqueue fc (%transfer w 0 (fake-address #x66) (nano 1/4)))
               (cl-ton::fakechain-advance fc 3)
               (check "without the library the external fails (missing library): balance untouched"
                      (= (cl-ton::fakechain-account-balance fc (wallet-address w)) (nano 10)))
               (cl-ton::fakechain-add-library fc (wallet-v5r1-code))
               (%fc-enqueue fc (%transfer w 0 (fake-address #x66) (nano 1/4)))
               (cl-ton::fakechain-advance fc 3)
               (check "with the library published the same external executes: balance dropped"
                      (< (cl-ton::fakechain-account-balance fc (wallet-address w)) (nano 10))))
          (cl-ton::stop-fakechain fc)))))

;;; --- a flaky, slow link between the proxy and the "liteserver" ---------------------------
;;;
;;; The public network is not the loopback.  A CHAOS RELAY sits between the proxy and the
;;; fakechain: it delays every chunk by a random amount and, every DROP-EVERY chunks of answers,
;;; resets the connection (a TCP session lost mid-query).  A real tonlib then synchronises and reads
;;; accounts THROUGH the proxy and two such relays.  Nothing here uses the network.

(defstruct (chaos-relay (:copier nil))
  listener port (stop nil) (dropped 0) (chunks 0) (lock (sb-thread:make-mutex)) threads)

(defun %relay-pump (relay from to drop-every jitter direction)
  "Copy FROM -> TO chunk by chunk with a random delay; on the answer direction (:UP) reset both
sockets every DROP-EVERY chunks."
  (let ((buf (make-array 65536 :element-type '(unsigned-byte 8))))
    (handler-case
        (loop until (chaos-relay-stop relay)
              do (multiple-value-bind (b len) (sb-bsd-sockets:socket-receive from buf nil)
                   (declare (ignore b))
                   (when (or (null len) (zerop len)) (return))
                   (when (plusp jitter) (sleep (random (float jitter))))
                   (let ((n (sb-thread:with-mutex ((chaos-relay-lock relay)) (incf (chaos-relay-chunks relay)))))
                     (when (and (eq direction :up) drop-every (zerop (mod n drop-every)))
                       (sb-thread:with-mutex ((chaos-relay-lock relay)) (incf (chaos-relay-dropped relay)))
                       (return)))
                   (cl-ton::adnl-socket-send-all to (subseq buf 0 len))))
      (error () nil))
    (ignore-errors (sb-bsd-sockets:socket-close from))
    (ignore-errors (sb-bsd-sockets:socket-close to))))

(defun start-chaos-relay (target-port &key (jitter 0.1) drop-every)
  (let* ((lsock (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp))
         (relay (make-chaos-relay :listener lsock)))
    (setf (sb-bsd-sockets:sockopt-reuse-address lsock) t)
    (sb-bsd-sockets:socket-bind lsock (sb-bsd-sockets:make-inet-address "127.0.0.1") 0)
    (sb-bsd-sockets:socket-listen lsock 16)
    (setf (chaos-relay-port relay) (nth-value 1 (sb-bsd-sockets:socket-name lsock)))
    (push (sb-thread:make-thread
           (lambda ()
             (handler-case
                 (loop until (chaos-relay-stop relay)
                       do (let* ((client (sb-bsd-sockets:socket-accept lsock))
                                 (up (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
                            (handler-case
                                (progn
                                  (sb-bsd-sockets:socket-connect up (sb-bsd-sockets:make-inet-address "127.0.0.1") target-port)
                                  (push (sb-thread:make-thread
                                         (lambda () (%relay-pump relay client up drop-every jitter :down))) (chaos-relay-threads relay))
                                  (push (sb-thread:make-thread
                                         (lambda () (%relay-pump relay up client drop-every jitter :up))) (chaos-relay-threads relay)))
                              (error () (ignore-errors (sb-bsd-sockets:socket-close client))
                                        (ignore-errors (sb-bsd-sockets:socket-close up))))))
               (error () nil)))
           :name "chaos relay accept")
          (chaos-relay-threads relay))
    relay))

(defun stop-chaos-relay (relay)
  (setf (chaos-relay-stop relay) t)
  (ignore-errors (sb-bsd-sockets:socket-close (chaos-relay-listener relay)))
  nil)

(defun test-tonlib-through-flaky-links ()
  (format t "tonlib -> NATIVE proxy -> two slow, flaky links -> fakechain~%")
  (if (not (%libs-available-p))
      (skip-missing "flaky-link resilience (tonlib/libemulator shared libraries)")
      (let* ((fc (cl-ton::start-fakechain))
             (dir (%tmpdir "chaos"))
             (cfg (format nil "~Afc.json" dir))
             (lib (%lib "tonlibjson-linux-x86_64.so"))
             (r1 (start-chaos-relay (cl-ton::fakechain-port fc) :jitter 0.25 :drop-every 30))
             (r2 (start-chaos-relay (cl-ton::fakechain-port fc) :jitter 0.25 :drop-every 45))
             proxy tl)
        (unwind-protect
             (progn
               (cl-ton::fakechain-advance fc 3)
               (cl-ton::fakechain-write-global-config fc cfg)
               ;; point the single liteserver entry at the two relays
               (let* ((text (uiop:read-file-string cfg))
                      (entry (cl-ton::fakechain-liteserver-entry fc))
                      (e1 (%replace-port entry (cl-ton::fakechain-port fc) (chaos-relay-port r1)))
                      (e2 (%replace-port entry (cl-ton::fakechain-port fc) (chaos-relay-port r2))))
                 (with-open-file (o cfg :direction :output :if-exists :supersede)
                   (write-string (%string-replace text entry (format nil "~A,~A" e1 e2)) o)))
               (setf proxy (cl-ton::open-proxy-liteserver :implementation :native :global-config cfg
                                                          :db (format nil "~Aproxy/" dir)))
               (check "flaky links: both relayed upstreams come up"
                      (cl-ton:proxy-wait-ready proxy :timeout (%scaled 20)))
               (setf tl (cl-ton::open-tonlib-via-proxy proxy cfg :library-path lib :sync nil))
               (let ((seqno (cl-ton:tonlib-sync tl :timeout (%scaled 60) :total-timeout (%scaled 120)
                                                   :progress (cl-ton:proxy-progress-function proxy))))
                 (check "flaky links: tonlib synchronises through them" (and seqno (>= seqno 3))))
               (let ((ok 0) (bad 0)
                     (addr (cl-ton:parse-address "0:1111111111111111111111111111111111111111111111111111111111111111")))
                 (dotimes (i 25)
                   (handler-case
                       (progn (cl-ton::retrying (lambda () (cl-ton:tonlib-account-state tl addr))
                                                :attempts 4 :delay 0.2)
                              (incf ok))
                     (error () (incf bad))))
                 ;; The relays reset a connection every N chunks of ANSWERS; how many chunks 25 reads
                 ;; produce depends on how TCP happens to segment them (and on machine load), so keep
                 ;; reading -- bounded -- until the chaos has really happened at least once.
                 (let ((extra 0))
                   (loop while (and (< extra 120)
                                    (zerop (+ (chaos-relay-dropped r1) (chaos-relay-dropped r2))))
                         do (incf extra)
                            (handler-case
                                (progn (cl-ton::retrying (lambda () (cl-ton:tonlib-account-state tl addr))
                                                         :attempts 4 :delay 0.2)
                                       (incf ok))
                              (error () (incf bad)))))
                 (check "flaky links: every account read succeeds (the app's retry included)"
                        (and (>= ok 25) (zerop bad))))
               (progn
                 (check "flaky links: the relays really did reset connections mid-run"
                        (plusp (+ (chaos-relay-dropped r1) (chaos-relay-dropped r2))))
                 ;; The relay counts a drop the moment it closes the sockets; the proxy notices that
                 ;; asynchronously (its reader thread sees the EOF), so give it a bounded moment
                 ;; instead of sampling the counters at the very instant of the drop.
                 (check "flaky links: the proxy saw them (a lost session or a failover, then recovery)"
                        (loop repeat (ceiling (* 50 (%scaled 5)))
                              do (let ((d (cl-ton:proxy-diagnostics proxy)))
                                   (when (or (plusp (reduce #'+ (getf d :upstreams)
                                                            :key (lambda (u) (getf u :failures))))
                                             (plusp (or (cl-ton::proxy-stat-value
                                                         (cl-ton::%native-of proxy) :failover) 0)))
                                     (return t)))
                                 (sleep 0.02)
                              finally (return nil)))
                 (check "flaky links: at the end the proxy still has a working upstream"
                        (cl-ton:proxy-wait-ready proxy :timeout (%scaled 20)))
                 (check "flaky links: the network summary has an opinion (answers were measured)"
                        (multiple-value-bind (k) (cl-ton:proxy-network-summary proxy)
                          (member k '(:fast :ok :slow :unknown))))))
          (ignore-errors (when tl (cl-ton::close-tonlib tl)))
          (ignore-errors (when proxy (cl-ton::close-proxy-liteserver proxy)))
          (stop-chaos-relay r1) (stop-chaos-relay r2)
          (cl-ton::stop-fakechain fc)
          (ignore-errors (uiop:delete-directory-tree (pathname dir) :validate t :if-does-not-exist :ignore))))))

(defun %string-replace (text old new)
  (let ((i (search old text)))
    (if i (concatenate 'string (subseq text 0 i) new (subseq text (+ i (length old)))) text)))

(defun %replace-port (entry old-port new-port)
  (%string-replace entry (format nil "\"port\":~D" old-port) (format nil "\"port\":~D" new-port)))
