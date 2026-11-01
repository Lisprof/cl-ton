;;;; tests/api.lisp -- the typed Lite API (LITE-EXECUTE) against real tonlib on one fakechain, the proofs its answers carry and
;;;; forged proofs; and the verdict channel of the proxy.

(in-package :cl-ton/test)

(defun %flipped-copy (octets index)
  (let ((copy (copy-seq octets)))
    (setf (aref copy index) (logxor #xFF (aref copy index)))
    copy))

(defun %fails-verification-p (proof)
  (handler-case (progn (cl-ton:verify-proof proof) nil)
    (cl-ton:ton-error () t)))

(defun %lite-account-id (address)
  (cl-ton::tl-make "liteServer.accountId" :workchain (cl-ton::address-workchain address) :id (cl-ton::address-hash address)))

(defun %lite-account-answer (lc address)
  "(VALUES ANSWER PROOF) of the typed liteServer.getAccountState of ADDRESS at the head LC proved."
  (cl-ton:lite-execute lc (cl-ton::tl-make "liteServer.getAccountState" :id (cl-ton::lite-sync lc)
                                                                       :account (%lite-account-id address))))

(defun %test-lite-proofs (lc)
  "Forged proofs of the config and the shards, as the typed Lite API hands them out, no longer verify."
  (multiple-value-bind (config proof)
      (cl-ton:lite-execute lc (cl-ton::tl-make "liteServer.getConfigAll" :mode 0 :id (cl-ton::lite-sync lc)))
    (check "getConfigAll: the proof is a clton.proofConfig that verifies and survives its TL bytes"
           (and (cl-ton::tl-is proof "clton.proofConfig")
                (cl-ton:verify-proof proof)
                (cl-ton::proof-p (cl-ton:octets->proof (cl-ton:proof->octets proof)))))
    (check "getConfigAll: a proof whose config proof was altered no longer verifies"
           (%fails-verification-p
            (cl-ton::tl-make "clton.proofConfig" :trusted (cl-ton:proof-trusted-block proof)
                                                 :answer (cl-ton::tl-make "liteServer.configInfo"
                                                                          :mode (cl-ton::tl-get config :mode) :id (cl-ton::tl-get config :id)
                                                                          :state-proof (cl-ton::tl-get config :state-proof)
                                                                          :config-proof (%flipped-copy (cl-ton::tl-get config :config-proof)
                                                                                                       (floor (length (cl-ton::tl-get config :config-proof)) 2)))))))
  (multiple-value-bind (shards proof)
      (cl-ton:lite-execute lc (cl-ton::tl-make "liteServer.getAllShardsInfo" :id (cl-ton::lite-sync lc)))
    (check "getAllShardsInfo: a proof whose shard data was altered no longer verifies"
           (and (cl-ton::tl-is proof "clton.proofAllShards") (cl-ton:verify-proof proof)
                (%fails-verification-p
                 (cl-ton::tl-make "clton.proofAllShards" :block (cl-ton::tl-get proof :block)
                                                         :answer (cl-ton::tl-make "liteServer.allShardsInfo"
                                                                                  :id (cl-ton::tl-get shards :id) :proof (cl-ton::tl-get shards :proof)
                                                                                  :data (%flipped-copy (cl-ton::tl-get shards :data)
                                                                                                       (floor (length (cl-ton::tl-get shards :data)) 2)))))))))

(defun test-lite-api-oracle ()
  (format t "lite API: typed answers with proofs, against real tonlib on one fakechain~%")
  (if (not (%libs-available-p))
      (skip-missing "the typed Lite API against tonlib (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (cl-ton:wallet-address w))
                (absent (fake-address #x5b)))
           (dotimes (seqno 3)
             (%fc-enqueue fc (%transfer w seqno (fake-address #x66) (cl-ton::nano 1/10)))
             (cl-ton::fakechain-advance fc 2))
           (cl-ton::fakechain-advance fc 4)
           (cl-ton::tonlib-sync tl)
           (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                  (lc (cl-ton::open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc))))
             (unwind-protect
                  (progn
                    (%lite-wait-ready lc)
                    (check "something that is not a lite API object is refused"
                           (handler-case (progn (cl-ton:lite-execute lc "liteServer.getTime") nil)
                             (cl-ton:ton-error () t)))
                    (check "a function the lite client does not run is refused by name"
                           (handler-case (progn (cl-ton:lite-execute lc (cl-ton::tl-make "liteServer.getState" :id (cl-ton::lite-sync lc))) nil)
                             (cl-ton:ton-error (e) (search "getState" (princ-to-string e)))))
                    (check "sendMessage: what is not an inbound external message is refused before sending"
                           (handler-case (progn (cl-ton:lite-execute lc (cl-ton::tl-make "liteServer.sendMessage"
                                                                                         :body (cl-ton:serialize-boc (cl-ton:end-cell (cl-ton:begin-cell)))))
                                                nil)
                             (cl-ton:ton-error () t)))
                    (%test-lite-proofs lc)
                    (dolist (a (list addr absent))
                      (let ((what (if (eq a addr) "the wallet" "an absent account")))
                        (multiple-value-bind (answer proof) (%lite-account-answer lc a)
                          (let* ((ts (cl-ton::tonlib-account-state tl a))
                                 (state (cl-ton::tl-get answer :state))
                                 (account (and (plusp (length state)) (cl-ton::parse-account (first (cl-ton::parse-boc state)))))
                                 (verified (cl-ton::lite-account-state lc a)))
                            (check (format nil "~A: the typed answer is a liteServer.accountState" what)
                                   (cl-ton::tl-is answer "liteServer.accountState"))
                            (check (format nil "~A: balance and last transaction are those of real tonlib" what)
                                   (and (= (cl-ton::account-state-balance ts) (if account (getf account :balance) 0))
                                        (= (cl-ton::account-state-last-lt ts) (if account (getf verified :last-trans-lt) 0))
                                        (or (null account)
                                            (equal (cl-ton::account-state-last-hash ts)
                                                   (cl-ton::base64-encode (getf verified :last-trans-hash))))))
                            (check (format nil "~A: the proof is a clton.proofAccountState and verifies again" what)
                                   (and (cl-ton::proof-p proof) (cl-ton::tl-is proof "clton.proofAccountState")
                                        (eq (and (getf (cl-ton:verify-proof proof) :exists) t) (eq a addr))))
                            (check (format nil "~A: the proof survives its TL bytes" what)
                                   (let ((again (cl-ton:octets->proof (cl-ton:proof->octets proof))))
                                     (and (cl-ton::proof-p again)
                                          (eq (and (getf (cl-ton:verify-proof again) :exists) t) (eq a addr)))))
                            (when (eq a addr)
                              (let ((forged (cl-ton::tl-make "clton.proofAccountState"
                                                             :trusted (cl-ton:proof-trusted-block proof)
                                                             :workchain (cl-ton::tl-get proof :workchain)
                                                             :account (cl-ton::tl-get proof :account)
                                                             :answer (cl-ton::tl-make "liteServer.accountState"
                                                                                      :id (cl-ton::tl-get answer :id) :shardblk (cl-ton::tl-get answer :shardblk)
                                                                                      :shard-proof (cl-ton::tl-get answer :shard-proof) :proof (cl-ton::tl-get answer :proof)
                                                                                      :state (%flipped-copy state (floor (length state) 2))))))
                                (check "a proof whose state was altered no longer verifies" (%fails-verification-p forged))))))))
                    (check "getTransactions: the chain from the wallet's last transaction has the three transfers"
                           (let* ((r (cl-ton::lite-account-state lc addr))
                                  (answer (cl-ton:lite-execute lc (cl-ton::tl-make "liteServer.getTransactions" :count 10 :account (%lite-account-id addr)
                                                                                                                 :lt (getf r :last-trans-lt) :hash (getf r :last-trans-hash)))))
                             (= (length (cl-ton::tl-get answer :ids))
                                (length (cl-ton::tonlib-transactions tl addr))))))
               (cl-ton::close-lite-client lc))))))))

;;; --- verdicts: a lying upstream behind the proxy ----------------------------------------------------------------------------

(defun %lying-handler (fc counter mode)
  "An ADNL-EXT-SERVER handler that answers as the fakechain FC does, except that the proofs of an account state it gives are
altered: always when MODE is :ALWAYS, and for the first answer only when :ONCE.  COUNTER is a cons whose car counts the lies."
  (lambda (server conn query-id query)
    (let ((answer (cl-ton::fakechain-handle-query fc server conn query-id query)))
      (handler-case
          (let* ((outer (cl-ton::tl-decode query))
                 (fn (cl-ton::tl-decode (nth-value 1 (cl-ton::proxy-split-query (cl-ton::tl-get outer :data)))))
                 (decoded (and (cl-ton::tl-is fn "liteServer.getAccountState") (cl-ton::tl-decode answer))))
            (if (and decoded (cl-ton::tl-is decoded "liteServer.accountState")
                     (plusp (length (cl-ton::tl-get decoded :state)))
                     (or (eq mode :always) (zerop (car counter))))
                (let ((state (cl-ton::tl-get decoded :state)))
                  (incf (car counter))
                  (cl-ton::tl-encode (cl-ton::tl-make "liteServer.accountState"
                                                      :id (cl-ton::tl-get decoded :id)
                                                      :shardblk (cl-ton::tl-get decoded :shardblk)
                                                      :shard-proof (cl-ton::tl-get decoded :shard-proof)
                                                      :proof (cl-ton::tl-get decoded :proof)
                                                      :state (%flipped-copy state (floor (length state) 2)))))
                answer))
        (error () answer)))))

(defun %proxy-upstream-by-port (native port)
  (find port (cl-ton::lisp-proxy-upstreams native) :key #'cl-ton::proxy-upstream-port))

(defun test-verdict-channel ()
  (format t "lite client -> proxy -> an honest and a lying upstream: verdicts~%")
  (if (not (%libs-available-p))
      (skip-missing "the verdict channel (emulator shared library)")
      (let* ((fc (cl-ton::start-fakechain))
             (dir (%tmpdir "verdict"))
             (cfg (format nil "~Afc.json" dir))
             (lies (list 0))
             (mode :once)
             (liar (cl-ton::start-adnl-ext-server :keypair (cl-ton::fakechain-keypair fc)
                                                  :handler (lambda (server conn query-id query)
                                                             (funcall (%lying-handler fc lies mode) server conn query-id query))))
             proxy lc)
        (unwind-protect
             (let* ((w (%seed-wallet fc))
                    (addr (cl-ton:wallet-address w)))
               (cl-ton::fakechain-advance fc 4)
               (cl-ton::fakechain-write-global-config fc cfg)
               (let* ((text (uiop:read-file-string cfg))
                      (entry (cl-ton::fakechain-liteserver-entry fc))
                      (liar-entry (%replace-port entry (cl-ton::fakechain-port fc) (cl-ton::adnl-ext-server-port liar))))
                 (with-open-file (o cfg :direction :output :if-exists :supersede)
                   (write-string (%string-replace text entry (format nil "~A,~A" entry liar-entry)) o)))
               (setf proxy (cl-ton::open-proxy-liteserver :implementation :native :global-config cfg
                                                          :db (format nil "~Aproxy/" dir)))
               (check "verdicts: both upstreams come up" (cl-ton::proxy-wait-ready proxy :timeout (%scaled 20)))
               (let* ((native (cl-ton::proxy-liteserver-native proxy))
                      (honest (%proxy-upstream-by-port native (cl-ton::fakechain-port fc)))
                      (liar-up (%proxy-upstream-by-port native (cl-ton::adnl-ext-server-port liar)))
                      (public (cl-ton::keypair-public (cl-ton::lisp-proxy-keypair native))))
                 (setf lc (cl-ton::open-lite-client "127.0.0.1" (cl-ton:proxy-liteserver-port proxy) public (%zero-block-id fc)))
                 (%lite-wait-ready lc)
                 (check "verdicts: both upstreams are known to the proxy" (and honest liar-up))
                 ;; phase 1: the first read goes to the liar (the honest upstream is avoided for a minute), which lies once
                 (setf (cl-ton::proxy-upstream-ban-until honest)
                       (+ (get-internal-real-time) (* 60 internal-time-units-per-second)))
                 (let ((state (handler-case (cl-ton::lite-account-state lc addr) (error () nil))))
                   (check "verdicts: the lie is caught and the read is repeated, giving the proved state"
                          (and state (getf state :exists) (= 1 (car lies))))
                   (check "verdicts: the proxy was told the answer did not verify"
                          (= 1 (cl-ton::proxy-stat-value native :verdict-rejected)))
                   (check "verdicts: the upstream that lied is avoided now"
                          (> (cl-ton::proxy-upstream-ban-until liar-up) (get-internal-real-time))))
                 ;; phase 2: the liar would lie every time, but it is not asked any more
                 (setf (cl-ton::proxy-upstream-ban-until honest) 0
                       (cl-ton::proxy-upstream-penalty-until honest) 0)
                 (setf mode :always)
                 (let ((ok 0))
                   (dotimes (i 8)
                     (when (handler-case (getf (cl-ton::lite-account-state lc addr) :exists) (error () nil)) (incf ok)))
                   (check "verdicts: while it is banned every read verifies and the liar is not asked again"
                          (and (= ok 8) (= 1 (car lies)))))
                 (check "verdicts: a verdict about an answer the proxy never gave is not known"
                        (not (cl-ton::lite-report-verdict lc (make-array 5 :element-type '(unsigned-byte 8) :initial-element 1)
                                                          nil "nothing")))))
          (ignore-errors (when lc (cl-ton::close-lite-client lc)))
          (ignore-errors (when proxy (cl-ton::close-proxy-liteserver proxy)))
          (ignore-errors (cl-ton::stop-adnl-ext-server liar))
          (ignore-errors (cl-ton::stop-fakechain fc))))))
