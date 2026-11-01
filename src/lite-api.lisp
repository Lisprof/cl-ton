;;;; lite-api.lisp -- the typed Lite API on the lite client: LITE-EXECUTE.
;;;;
;;;; One entry point takes a typed lite API function object (what TL-MAKE builds from lite_api.tl: "liteServer.getAccountState",
;;;; ...) and returns (VALUES ANSWER PROOF): ANSWER the typed lite API object the function returns -- the answer a liteserver
;;;; would give, but only after the lite client verified it against the chain it trusts -- and PROOF the clton.Proof of what it
;;;; verified (NIL where the answer carries none, say what the server reports of itself).  Same shape as TONLIB-EXECUTE, but the
;;;; objects are the lite API's own: this is the interface the application and its tests use.  A table from the function name
;;;; to the function that runs it; no generic function.

(in-package :cl-ton)

(defvar *lite-execute-table* (make-hash-table :test 'equal)
  "Function name (a lite_api function) -> function of (CLIENT REQUEST) returning (VALUES ANSWER PROOF).")

(defmacro def-lite-function (name (client request) &body body)
  "Define how LITE-EXECUTE runs the lite API function NAME."
  `(setf (gethash ,name *lite-execute-table*)
         (lambda (,client ,request) (declare (ignorable ,client ,request)) ,@body)))

(defun lite-execute-supported ()
  "The names of the lite API functions LITE-EXECUTE runs, sorted."
  (sort (loop for name being the hash-keys of *lite-execute-table* collect name) #'string<))

(defun lite-execute (client request &key min-seqno)
  "Run REQUEST, a typed lite API function object, on CLIENT (a lite client): (VALUES ANSWER PROOF).  Signals for an object that
is not a function of the lite API, one the client does not run, or an answer that does not verify.  With MIN-SEQNO the freshness
floor is ENFORCED: the request runs only once the head the client PROVED is at or above that masterchain seqno (the client waits
for it, as liteServer.waitMasterchainSeqno does, and signals when no liteserver gets there); nothing reads state older than it."
  (unless (tl-obj-p request) (ton-error "not a lite API object: ~S" request))
  (let ((function (gethash (tl-obj-name request) *lite-execute-table*)))
    (unless function
      (ton-error "the lite function ~A is not supported by the lite client" (tl-obj-name request)))
    (when min-seqno (lite-sync client :min-seqno min-seqno))
    (funcall function client request)))

(defun %lite-zero-octets (n) (make-array n :element-type '(unsigned-byte 8) :initial-element 0))

(defun %lite-request-address (account)
  "The ADDRESS of a typed liteServer.accountId."
  (make-address :workchain (tl-get account :workchain) :hash (coerce (tl-get account :id) 'octets)))

(defun %lite-zero-state-id (client)
  (let ((anchor (lite-client-anchor client)))
    (tl-make "tonNode.zeroStateIdExt" :workchain (tl-get anchor :workchain)
                                      :root-hash (tl-get anchor :root-hash) :file-hash (tl-get anchor :file-hash))))

;;; --- shared helpers -------------------------------------------------------------------------------------------------------------

(defun %lite-block-header-of (client lite-id)
  "The proved header of the block LITE-ID (a lite API tonNode.blockIdExt): a plist (:BLOCK-ID lite id :ANSWER the verified
liteServer.blockHeader :GLOBAL-ID n :INFO BlockInfo plist :CELL the Block cell :PREV previous blocks :FIELDS the BlockInfo
header bits).  The block is checked to be of the trusted chain by the caller (%LITE-BIND-BLOCK)."
  (let* ((answer (lite-call client (tl-make "liteServer.getBlockHeader" :id lite-id :mode 0))))
    (with-proof-errors
      (%prove-same-block-id (tl-get answer :id) lite-id "the block header")
      (let* ((block (verify-merkle-proof (%single-root (tl-get answer :header-proof) "block header") (tl-get lite-id :root-hash)))
             (info-cell (svref (cell-refs block) 0))
             (info (parse-block-info info-cell))
             (prev (parse-block-links block lite-id))
             (bs (cell-slice block))
             (global-id (multiple-value-bind (tag s) (load-uint bs 32)
                          (%prove (= tag #x11ef55aa) "not a Block cell")
                          (load-int s 32)))
             (s (skip-bits (cell-slice info-cell) 32)))
        (multiple-value-bind (version s) (load-uint s 32)
          (let ((s (skip-bits s 1)))                                ; not_master
            (multiple-value-bind (after-merge s) (load-uint s 1)
              (multiple-value-bind (before-split s) (load-uint s 1)
                (multiple-value-bind (after-split s) (load-uint s 1)
                  (multiple-value-bind (want-split s) (load-uint s 1)
                    (multiple-value-bind (want-merge s) (load-uint s 1)
                      (let ((s (skip-bits s 2)))                    ; key_block (also in INFO), vert_seqno_incr
                        (multiple-value-bind (flags s) (load-uint s 8)
                          (let ((s (skip-bits s 32)))               ; seq_no
                            (multiple-value-bind (vert-seqno s) (load-uint s 32)
                              ;; shard ident (104 bits), gen_utime, start_lt, end_lt, validator list hash, catchain seqno
                              (let ((s (skip-bits s (+ 104 32 64 64 32 32))))
                                (multiple-value-bind (min-ref s) (load-uint s 32)
                                  (let ((prev-key (load-uint s 32)))
                                    (list :block-id lite-id :answer answer :global-id global-id :info info :cell block :prev prev
                                          :fields (list :version version :after-merge (= after-merge 1)
                                                        :before-split (= before-split 1) :after-split (= after-split 1)
                                                        :want-split (= want-split 1) :want-merge (= want-merge 1)
                                                        :flags flags :vert-seqno vert-seqno
                                                        :min-ref-mc-seqno min-ref :prev-key-block-seqno prev-key))))))))))))))))))))

(defun external-message-hash-norm (octets)
  "The NORMALIZED hash of the inbound external message in the BoC OCTETS (TEP-467, what raw.sendMessageReturnHash reports as
hash_norm): the hash of the message with the source set to addr_none, the import fee to 0, no StateInit and the body always
stored as a reference.  Two copies of one message that differ only in those parts have the same normalized hash.  Signals
for anything that is not an inbound external message, or whose StateInit is written inline."
  (handler-case
      (let ((s (cell-slice (first (parse-boc octets)))))
        (multiple-value-bind (tag s) (load-uint s 2)
          (unless (= tag 2) (ton-error "the message is not an inbound external one"))
          (multiple-value-bind (src s) (load-uint s 2)
            (setf s (case src
                      (0 s)
                      (1 (multiple-value-bind (len s) (load-uint s 9) (skip-bits s len)))
                      (t (ton-error "the source of the message is not an external address"))))
            (multiple-value-bind (dest-head s) (load-uint s 3)
              (unless (= dest-head 4) (ton-error "the destination is not a plain standard address"))
              (multiple-value-bind (workchain s) (load-uint s 8)
                (multiple-value-bind (account s) (load-uint s 256)
                  (multiple-value-bind (fee s) (load-coins s)
                    (declare (ignore fee))
                    (multiple-value-bind (has-init s) (load-bit s)
                      (when has-init
                        (multiple-value-bind (init-in-ref s2) (load-bit s)
                          (unless init-in-ref (ton-error "a StateInit written inline is not supported"))
                          (setf s (nth-value 1 (load-ref s2)))))
                      (multiple-value-bind (body-in-ref s) (load-bit s)
                        (let ((body (if body-in-ref
                                        (load-ref s)
                                        (let ((b (begin-cell)))
                                          (multiple-value-bind (bits n) (slice-rest-bits s)
                                            (when (plusp n) (setf b (store-uint b bits n))))
                                          (loop for i from (slice-ref-pos s) below (length (cell-refs (slice-cell s)))
                                                do (setf b (store-ref b (aref (cell-refs (slice-cell s)) i))))
                                          (end-cell b)))))
                          (let ((b (begin-cell)))
                            (setf b (store-uint b 2 2))
                            (setf b (store-uint b 0 2))
                            (setf b (store-uint b 4 3))
                            (setf b (store-uint b workchain 8))
                            (setf b (store-uint b account 256))
                            (setf b (store-uint b 0 4))
                            (setf b (store-bit b 0))
                            (setf b (store-bit b 1))
                            (setf b (store-ref b body))
                            (hex->octets (cell-hash-hex (end-cell b))))))))))))))
    (error (e) (ton-error "liteServer.sendMessage: ~A" e))))

;;; --- the masterchain head, time, version -------------------------------------------------------------------------------------

(def-lite-function "liteServer.getMasterchainInfo" (client request)
  ;; LAST is the head the client proved itself; the liteserver's state root hash is not proved, so it is left zero
  (values (tl-make "liteServer.masterchainInfo" :last (lite-sync client) :state-root-hash (%lite-zero-octets 32)
                                                :init (%lite-zero-state-id client))
          nil))

(def-lite-function "liteServer.getMasterchainInfoExt" (client request)
  ;; LAST and LAST_UTIME are proved (the header of the head); VERSION, CAPABILITIES and NOW are what the liteserver reports
  (let* ((server (lite-call client (tl-make "liteServer.getMasterchainInfoExt" :mode (tl-get request :mode))))
         (head (lite-sync client))
         (header (%lite-block-header-of client head)))
    (values (tl-make "liteServer.masterchainInfoExt" :mode (tl-get request :mode)
                                                     :version (tl-get server :version)
                                                     :capabilities (tl-get server :capabilities)
                                                     :last head
                                                     :last-utime (getf (getf header :info) :gen-utime)
                                                     :now (tl-get server :now)
                                                     :state-root-hash (%lite-zero-octets 32)
                                                     :init (%lite-zero-state-id client))
            nil)))

(def-lite-function "liteServer.getTime" (client request)
  (values (lite-call client request) nil))                ; the server's clock: nothing proves it

(def-lite-function "liteServer.getVersion" (client request)
  (values (lite-call client request) nil))                ; what the server says of itself: nothing proves it

;;; --- accounts ------------------------------------------------------------------------------------------------------------------

(def-lite-function "liteServer.getAccountState" (client request)
  (let* ((state (lite-account-state client (%lite-request-address (tl-get request :account)) :block (tl-get request :id)))
         (proof (getf state :proof)))
    (values (tl-get proof :answer) proof)))

(def-lite-function "liteServer.getTransactions" (client request)
  ;; the newest COUNT transactions from the transaction id (LT, HASH) of the account, each chained to the one before
  (let* ((address (%lite-request-address (tl-get request :account)))
         (result (lite-transactions client address :count (tl-get request :count)
                                                   :from-lt (tl-get request :lt) :from-hash (tl-get request :hash)))
         (proof (getf result :proof)))
    (values (if proof
                (tl-get proof :answer)
                (tl-make "liteServer.transactionList" :ids '() :transactions (%lite-zero-octets 0)))
            proof)))

(def-lite-function "liteServer.runSmcMethod" (client request)
  ;; the getter is run by the client's own emulator on the PROVED account state with the proved configuration and the public
  ;; libraries; the answer is the result it computed (mode bit 2), never the server's word for it
  (let* ((address (%lite-request-address (tl-get request :account)))
         (block (tl-get request :id))
         (state (lite-account-state client address :block block))
         (params (tl-get request :params))
         (stack (and params (plusp (length params)) (parse-vm-stack (first (parse-boc params))))))
    (multiple-value-bind (items exit-code gas proof) (lite-backend-run-with-proof client state (tl-get request :method-id) stack block)
      (declare (ignore gas))
      (values (tl-make "liteServer.runMethodResult"
                       :mode (logand (tl-get request :mode) 4)
                       :id (proof-trusted-block (getf state :proof))
                       :shardblk (tl-get (tl-get (getf state :proof) :answer) :shardblk)
                       :exit-code exit-code
                       :result (serialize-boc (list (serialize-vm-stack items)) :has-crc32c nil))
              proof))))

;;; --- blocks ---------------------------------------------------------------------------------------------------------------------

(def-lite-function "liteServer.getBlockHeader" (client request)
  (let ((header (%lite-block-header-of client (tl-get request :id))))
    (%lite-bind-block client (getf header :block-id))
    (values (getf header :answer) nil)))

(def-lite-function "liteServer.lookupBlock" (client request)
  ;; MODE 1 the seqno of ID, 2 the logical time LT, 4 the unix time UTIME (exactly one), in the workchain and shard of ID
  (let* ((mode (tl-get request :mode))
         (id (tl-get request :id))
         (found (lite-lookup-block client (tl-get id :workchain) (ldb (byte 64 0) (tl-get id :shard))
                                   :seqno (and (logtest mode 1) (tl-get id :seqno))
                                   :lt (and (logtest mode 2) (tl-get request :lt))
                                   :utime (and (logtest mode 4) (tl-get request :utime))))
         (header (%lite-block-header-of client (getf found :block-id))))
    (values (getf header :answer) nil)))

(def-lite-function "liteServer.getAllShardsInfo" (client request)
  (multiple-value-bind (shards proof) (lite-backend-shards client (lite-block-id->tlapi (tl-get request :id)))
    (declare (ignore shards))
    (values (tl-get proof :answer) proof)))

(def-lite-function "liteServer.getConfigAll" (client request)
  (multiple-value-bind (config proof) (lite-backend-config-with-proof client (tl-get request :id))
    (declare (ignore config))
    (values (tl-get proof :answer) proof)))

;;; --- sending --------------------------------------------------------------------------------------------------------------------

(def-lite-function "liteServer.sendMessage" (client request)
  ;; STATUS 1 is the liteserver's acceptance into its pool, not inclusion in a block
  (external-message-hash-norm (tl-get request :body))    ; refuses what is not an inbound external message, before sending
  (lite-send-message client (tl-get request :body))
  (values (tl-make "liteServer.sendMsgStatus" :status 1) nil))

;;; --- the rest of the proved reads ------------------------------------------------------------------------------------------------

(defun %lite-trusted-mc (client id)
  "The masterchain block ID the request names, proved to be of the chain CLIENT trusts (the head itself costs nothing)."
  (if id (%lite-pinned client id) (lite-sync client)))

(def-lite-function "liteServer.getConfigParams" (client request)
  ;; the parameters asked for are revealed and checked by VERIFY-CONFIG-INFO; no clton proof object carries a PART of a
  ;; configuration (clton.proofConfig is the whole one), so the answer comes without one
  (let* ((trusted (%lite-trusted-mc client (tl-get request :id)))
         (params (coerce (tl-get request :param-list) 'list)))
    (multiple-value-bind (verified answer)
        (lite-call-verified client (tl-make "liteServer.getConfigParams" :mode (tl-get request :mode) :id trusted
                                                                         :param-list (tl-get request :param-list))
                            (lambda (a) (verify-config-info a trusted :params params)))
      (declare (ignore verified))
      (values answer nil))))

(def-lite-function "liteServer.listBlockTransactions" (client request)
  ;; ONE page of the transactions of the block, each id proved to be in it; the proof is always asked for (mode bit 32)
  (let* ((id (tl-get request :id))
         (mode (logior (tl-get request :mode) 32))
         (count (min (tl-get request :count) 256))
         (reverse (logtest mode 64)))
    (%lite-trust-block client id)
    (multiple-value-bind (verified answer)
        (lite-call-verified client (apply #'tl-make "liteServer.listBlockTransactions" :id id :mode mode :count count
                                          (and (logtest mode 128) (list :after (tl-get request :after))))
                            (lambda (a) (verify-block-transactions a id :count count :reverse reverse)))
      (declare (ignore verified))
      (values answer (make-block-transactions-proof id reverse (list (cons count answer)))))))

(def-lite-function "liteServer.getLibraries" (client request)
  ;; the public libraries of the masterchain among the hashes, proved by the newest proved state; absent ones are left out
  (let ((found (lite-libraries client (coerce (tl-get request :library-list) 'list))))
    (values (tl-make "liteServer.libraryResult"
                     :result (mapcar (lambda (entry)
                                       (tl-make "liteServer.libraryEntry" :hash (coerce (car entry) 'tl-octets)
                                                                          :data (serialize-boc (cdr entry))))
                                     found))
            nil)))

(def-lite-function "liteServer.getLibrariesWithProof" (client request)
  (let* ((trusted (%lite-trusted-mc client (tl-get request :id)))
         (hashes (coerce (tl-get request :library-list) 'list))
         (mode (tl-get request :mode)))
    (multiple-value-bind (verified answer)
        (lite-call-verified client (tl-make "liteServer.getLibrariesWithProof" :id trusted :mode mode
                                                                               :library-list (tl-get request :library-list))
                            (lambda (a) (verify-libraries-with-proof a trusted hashes :mode mode)))
      (declare (ignore verified))
      (values answer nil))))

(def-lite-function "liteServer.getShardInfo" (client request)
  (let* ((trusted (%lite-trusted-mc client (tl-get request :id)))
         (workchain (tl-get request :workchain))
         (shard (ldb (byte 64 0) (tl-get request :shard)))
         (exact (and (tl-get request :exact) t)))
    (multiple-value-bind (verified answer)
        (lite-call-verified client (tl-make "liteServer.getShardInfo" :id trusted :workchain workchain
                                                                      :shard (%lite-signed-shard shard) :exact exact)
                            (lambda (a) (verify-shard-info a trusted workchain shard :exact exact)))
      (declare (ignore verified))
      (values answer nil))))

(def-lite-function "liteServer.getBlockProof" (client request)
  ;; the chain of links from the KNOWN block (proved first) towards the target, each link checked
  (let* ((known (%lite-pinned client (tl-get request :known-block)))
         (answer (lite-call client (apply #'tl-make "liteServer.getBlockProof" :mode (tl-get request :mode) :known-block known
                                          (and (logtest (tl-get request :mode) 1) (list :target-block (tl-get request :target-block)))))))
    (verify-partial-block-proof answer known)
    (values answer nil)))

(def-lite-function "liteServer.getShardBlockProof" (client request)
  ;; the links from a masterchain block to the shard block, and that masterchain block placed in the trusted chain
  (let* ((id (tl-get request :id))
         (answer (lite-call client (tl-make "liteServer.getShardBlockProof" :id id)))
         (mc (getf (verify-shard-block-proof answer id) :mc-block)))
    (lite-prove-block client mc)
    (values answer nil)))

(def-lite-function "liteServer.getOneTransaction" (client request)
  ;; the transaction of the account at the logical time LT in the block, proved to be in it
  (let ((id (tl-get request :id))
        (account (coerce (tl-get (tl-get request :account) :id) 'octets)))
    (%lite-trust-block client id)
    (multiple-value-bind (verified answer)
        (lite-call-verified client request
                            (lambda (a) (verify-one-transaction a id account (tl-get request :lt))))
      (declare (ignore verified))
      (values answer nil))))

(def-lite-function "liteServer.listBlockTransactionsExt" (client request)
  ;; ONE page of the FULL transactions of the block, each bound to the block by its hash
  (let* ((id (tl-get request :id))
         (mode (logior (tl-get request :mode) 32))
         (count (min (tl-get request :count) 256))
         (reverse (logtest mode 64)))
    (%lite-trust-block client id)
    (multiple-value-bind (verified answer)
        (lite-call-verified client (apply #'tl-make "liteServer.listBlockTransactionsExt" :id id :mode mode :count count
                                          (and (logtest mode 128) (list :after (tl-get request :after))))
                            (lambda (a) (verify-block-transactions-ext a id :count count :reverse reverse)))
      (declare (ignore verified))
      (values answer nil))))

(def-lite-function "liteServer.getBlock" (client request)
  ;; the whole block, bound to the trusted chain by its id: the data hashes to the file hash, its root to the root hash
  (let ((id (tl-get request :id)))
    (%lite-trust-block client id)
    (multiple-value-bind (verified answer)
        (lite-call-verified client request (lambda (a) (verify-block-data a id)))
      (declare (ignore verified))
      (values answer nil))))
