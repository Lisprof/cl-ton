(in-package :cl-ton)

;;; The verifying lite client as a drop-in for the tonlib client (plan R2b).
;;;
;;; The application reads the chain through the TONLIB-* functions of tonlib.lisp.  When their first
;;; argument is a LITE-CLIENT instead of a tonlib client, they call the LITE-BACKEND-* functions here,
;;; which return EXACTLY what the tonlib versions return (the same structs, cells, alists and the
;;; same JSON-shaped block ids), but every answer has been verified by the lite client against the
;;; masterchain block it trusts, with no tonlibjson and no JSON round trip.  Not served yet (still
;;; tonlib only): TONLIB-SHARDS, TONLIB-BLOCK-TRANSACTIONS, TONLIB-TRANSACTIONS (they return raw
;;; tonlib JSON documents).

(defun %zero-hash-base64 () (base64-encode (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))

(defun lite-block-id->json (id)
  "A blockIdExt tl-obj as the JSON-shaped hash table tonlib returns (ton.blockIdExt)."
  (let ((h (make-hash-table :test 'equal)))
    (setf (gethash "@type" h) "ton.blockIdExt"
          (gethash "workchain" h) (tl-get id :workchain)
          (gethash "shard" h) (format nil "~D" (let ((s (ldb (byte 64 0) (tl-get id :shard))))
                                                  (if (>= s (expt 2 63)) (- s (expt 2 64)) s)))
          (gethash "seqno" h) (tl-get id :seqno)
          (gethash "root_hash" h) (base64-encode (tl-get id :root-hash))
          (gethash "file_hash" h) (base64-encode (tl-get id :file-hash)))
    h))

(defun lite-backend-masterchain-block (lc)
  "The newest PROVED masterchain block, as TONLIB-MASTERCHAIN-BLOCK returns it."
  (lite-block-id->json (lite-sync lc)))

(defun lite-backend-masterchain-info (lc)
  (tl-get (lite-sync lc) :seqno))

(defun lite-backend-account-state (lc addr)
  "As TONLIB-ACCOUNT-STATE: an ACCOUNT-STATE.  The state is proved; SYNC-UTIME is 0 (not proved, unused)."
  (let ((r (lite-account-state lc addr)))
    (if (not (getf r :exists))
        (make-account-state :address addr :balance 0 :code nil :data nil :last-lt 0
                            :last-hash (%zero-hash-base64) :status :uninit :sync-utime 0)
        (let ((account (parse-account (getf r :account-cell))))
          (make-account-state :address addr :balance (max 0 (or (getf account :balance) 0))
                              :code (getf account :code) :data (getf account :data)
                              :last-lt (getf r :last-trans-lt)
                              :last-hash (base64-encode (getf r :last-trans-hash))
                              :status (case (getf account :status)
                                        (:active :active) (:frozen :frozen) (t :uninit))
                              :sync-utime 0)))))

(defun lite-backend-config-cell (lc &optional block)
  "As TONLIB-CONFIG-CELL: the whole configuration dictionary, proved against the trusted block (or BLOCK, a pinned
one).  The configuration of a block never changes, so the last one fetched is kept: the observe mode reads a dozen
pools at one pinned block and asks for it once."
  (let* ((trusted (if block (%lite-pinned lc block) (lite-sync lc)))
         (key (list (tl-get trusted :seqno) (tl-get trusted :root-hash)))
         (cached (sb-thread:with-mutex ((lite-client-lock lc)) (lite-client-config-cache lc))))
    (if (and cached (equalp key (car cached)))
        (cdr cached)
        (let* ((answer (lite-call lc (tl-make "liteServer.getConfigAll" :mode 0 :id trusted)))
               (cell (getf (verify-config-info answer trusted :all t) :config-root)))
          (sb-thread:with-mutex ((lite-client-lock lc)) (setf (lite-client-config-cache lc) (cons key cell)))
          cell))))

(defun lite-backend-shard-account-cell (lc addr)
  "As TONLIB-SHARD-ACCOUNT-CELL: the ShardAccount cell (the proved account, its last transaction's
hash and lt) the emulator takes as its account input."
  (let ((r (lite-account-state lc addr)))
    (end-cell (if (getf r :exists)
                  (store-uint (store-bytes (store-ref (begin-cell) (getf r :account-cell)) (getf r :last-trans-hash))
                              (getf r :last-trans-lt) 64)
                  (store-uint (store-bytes (store-ref (begin-cell) (end-cell (store-bit (begin-cell) 0)))
                                           (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))
                              0 64)))))

(defun lite-backend-libraries (lc hashes)
  "As TONLIB-LIBRARIES: an alist of (hash-hex . cell) for the published libraries among HASHES."
  (mapcar (lambda (e) (cons (octets->hex (car e)) (cdr e)))
          (lite-libraries lc (mapcar (lambda (h) (as-octets h)) hashes))))

(defun lite-backend-send-message (lc message-cell)
  "As TONLIB-SEND-MESSAGE: hand the external message to the liteserver, return its hash as base64."
  (base64-encode (lite-send-message lc (serialize-boc message-cell))))

(defun lite-backend-libraries-for (lc hashes)
  "The libraries of HASHES (hex strings) as an alist (hex . cell): from the client's cache, the rest asked for
through LITE-BACKEND-LIBRARIES (proved against the masterchain state) and cached -- a library is named by its
own hash, so what was proved once stays right.  Signals when a node does not publish one."
  (let ((missing (remove-if (lambda (h) (sb-thread:with-mutex ((lite-client-lock lc)) (gethash h (lite-client-libraries lc))))
                            hashes)))
    (when missing
      (let ((found (lite-backend-libraries lc (mapcar #'hex->octets missing))))
        (dolist (h missing)
          (let ((hit (assoc h found :test #'string-equal)))
            (unless hit (ton-error "library ~A is not published in the masterchain" h))
            (sb-thread:with-mutex ((lite-client-lock lc)) (setf (gethash h (lite-client-libraries lc)) (cdr hit)))))))
    (loop for h in hashes
          collect (cons h (sb-thread:with-mutex ((lite-client-lock lc)) (gethash h (lite-client-libraries lc)))))))

(defvar *getter-log* nil
  "NIL, or a cons whose CAR collects (ADDRESS METHOD STACK ITEMS EXIT-CODE BLOCK) of every getter LITE-BACKEND-RUN-GET-METHOD
runs, newest first: what the trial compares with the liteserver's own answers.  Conveyed to PMAP workers (the pools are
read in parallel threads), so entries are pushed atomically.")
(pushnew '*getter-log* *pmap-conveyed*)

(defun lite-backend-run-get-method (lc addr method &optional stack)
  "As TONLIB-RUN-GET-METHOD: (VALUES ITEMS EXIT-CODE), the getter run in the emulator on the PROVED
account state with the proved configuration, and the public libraries the contract's code or data refer to
(STON.fi's pool code is one: a library cell) fetched and proved.  Like tonlib's, it honours *GET-METHOD-BLOCK*:
when that is bound (the observe mode pins every pool read to one block) the state and the configuration are
those of that masterchain block, proved to be of the trusted chain, not of whatever the newest head is by then."
  (let* ((block (and *get-method-block* (json->lite-block-id *get-method-block*)))
         (state (lite-account-state lc addr :block block))
         (account (and (getf state :exists) (parse-account (getf state :account-cell))))
         (hashes (and account (collect-library-hashes (getf account :code) (getf account :data)))))
    (let ((run (multiple-value-list
                (run-account-get-method (getf state :account-cell) method stack
                                        :config (lite-backend-config-cell lc block)
                                        :libraries (and hashes (lite-backend-libraries-for lc hashes))))))
      (when *getter-log*
        (sb-ext:atomic-push (list addr method stack (first run) (second run) block) (car *getter-log*)))
      (values-list run))))

;;; --- raw.transaction documents, shards and block transactions ------------------------------------
;;;
;;; The scanner and the transaction tracker read tonlib's JSON documents.  These build the same
;;; documents from PROVED cells.  raw.message's msg_data is always msg.dataRaw here (tonlib may
;;; present a text comment as msg.dataText), and a StateInit written inline in a message is not
;;; extracted into init_state (it is "" then).

(defun %json-table (&rest plist)
  (let ((h (make-hash-table :test 'equal)))
    (loop for (k v) on plist by #'cddr do (setf (gethash k h) v))
    h))

(defun json->lite-block-id (json)
  "The ton.blockIdExt JSON-shaped hash table JSON as a blockIdExt tl-obj."
  (let ((shard (json-get json "shard")))
    (tl-block-id-ext :workchain (json-get json "workchain")
                     :shard (if (stringp shard) (parse-integer shard) shard)
                     :seqno (json-get json "seqno")
                     :root-hash (base64-decode (json-get json "root_hash"))
                     :file-hash (base64-decode (json-get json "file_hash")))))

(defun %friendly (addr) (if addr (address->string addr) ""))

(defun %message-json (msg)
  "A Message cell as tonlib's raw.message."
  (let* ((s (cell-slice msg))
         (internal (zerop (load-uint s 1)))
         (src nil) (dest nil) (value 0) (ihr 0) (fwd 0) (created 0))
    (let ((s (skip-bits s 1)))
      (if internal
          (let ((s (skip-bits s 3)))
            (multiple-value-bind (a s) (handler-case (load-address s) (error () (values nil (skip-bits s 2))))
              (setf src a)
              (multiple-value-bind (b s) (load-address s)
                (setf dest b)
                (multiple-value-bind (v s) (load-coins s)
                  (setf value v)
                  (let ((s (nth-value 1 (load-maybe-ref s))))
                    (multiple-value-bind (i s) (load-coins s)
                      (setf ihr i)
                      (multiple-value-bind (f s) (load-coins s)
                        (setf fwd f)
                        (multiple-value-bind (c s) (load-uint s 64)
                          (setf created c s (skip-bits s 32))))))))))
          (let ((s (skip-bits s 1)))                    ; ext_in (10) / ext_out (11)
            (multiple-value-bind (a s) (handler-case (load-address s) (error () (values nil (skip-bits s 2))))
              (setf src a)
              (multiple-value-bind (b s) (handler-case (load-address s) (error () (values nil (skip-bits s 2))))
                (setf dest b)
                (let ((tag2 (load-uint (skip-bits (cell-slice msg) 1) 1)))
                  (if (zerop tag2)
                      (setf fwd 0 s (nth-value 1 (load-coins s)))        ; import_fee
                      (setf created (load-uint s 64) s (skip-bits s 96)))))))))
    ;; init and body, from the position after the header: re-derive it by parsing again
    (multiple-value-bind (init-cell body) (%message-init-and-body msg)
      (%json-table "@type" "raw.message"
                   "hash" (base64-encode (node-hash-at msg 0))
                   "source" (%json-table "@type" "accountAddress" "account_address" (%friendly src))
                   "destination" (%json-table "@type" "accountAddress" "account_address" (%friendly dest))
                   "value" (format nil "~D" value)
                   "extra_currencies" nil
                   "fwd_fee" (format nil "~D" fwd)
                   "ihr_fee" (format nil "~D" ihr)
                   "created_lt" (format nil "~D" created)
                   "body_hash" (base64-encode (node-hash-at body 0))
                   "msg_data" (%json-table "@type" "msg.dataRaw"
                                           "body" (cell->base64 body)
                                           "init_state" (if init-cell (cell->base64 init-cell) ""))))))

(defun %message-init-and-body (msg)
  "(VALUES INIT-CELL-OR-NIL BODY-CELL) of a Message cell."
  (let* ((s (cell-slice msg)) (tag (load-uint s 1)))
    (let ((s (skip-bits s 1)))
      (multiple-value-bind (s)
          (if (zerop tag)
              (let* ((s (skip-bits s 3)))
                (multiple-value-bind (a s) (handler-case (load-address s) (error () (values nil (skip-bits s 2))))
                  (declare (ignore a))
                  (multiple-value-bind (b s) (load-address s)
                    (declare (ignore b))
                    (let* ((s (nth-value 1 (load-coins s))) (s (nth-value 1 (load-maybe-ref s)))
                           (s (nth-value 1 (load-coins s))) (s (nth-value 1 (load-coins s))))
                      (skip-bits s 96)))))
              (let ((s (skip-bits s 1)))              ; ext_in (10): src dest import_fee; ext_out (11): src dest created_lt created_at
                (multiple-value-bind (a s) (handler-case (load-address s) (error () (values nil (skip-bits s 2))))
                  (declare (ignore a))
                  (multiple-value-bind (b s) (handler-case (load-address s) (error () (values nil (skip-bits s 2))))
                    (declare (ignore b))
                    (if (zerop (load-uint (skip-bits (cell-slice msg) 1) 1))
                        (nth-value 1 (load-coins s))
                        (skip-bits s 96))))))
        (multiple-value-bind (has-init s) (load-bit s)
          (let ((init nil))
            (when has-init
              (multiple-value-bind (by-ref s2) (load-bit s)
                (if by-ref
                    (multiple-value-bind (c s3) (load-ref s2) (setf init c s s3))
                    ;; an inline StateInit: split_depth, special, code, data, library
                    (let ((s s2))
                      (multiple-value-bind (h s3) (load-bit s) (setf s (if h (skip-bits s3 5) s3)))
                      (multiple-value-bind (h s3) (load-bit s) (setf s (if h (skip-bits s3 2) s3)))
                      (dotimes (i 3) (setf s (nth-value 1 (load-maybe-ref s))))))))
            (multiple-value-bind (in-ref s) (load-bit s)
              (values init (if in-ref (values (load-ref s)) (cell-from-slice-rest s))))))))))

(defun %transaction-json (addr cell)
  "A Transaction CELL (already proved) as tonlib's raw.transaction.  As in tonlib, \"fee\" is the
transaction's total fees plus the forwarding and IHR fees of its outgoing messages, \"other_fee\" that
minus the storage fee.  \"data\" is the transaction cell as a BoC (tonlib's byte layout of the BoC may differ)."
  (let* ((s (cell-slice cell)))
    (unless (= (load-uint s 4) #b0111) (ton-error "not a transaction cell"))
    (let ((s (skip-bits s 4)))
      (multiple-value-bind (acct s) (load-bytes s 32)
        (declare (ignore acct))
        (multiple-value-bind (lt s) (load-uint s 64)
          (let ((s (skip-bits s 256 )))                    ; prev_trans_hash
            (let ((s (skip-bits s 64)))                    ; prev_trans_lt
              (multiple-value-bind (now s) (load-uint s 32)
                (let ((s (skip-bits (nth-value 1 (load-uint s 15)) 4)))   ; outmsg_cnt, statuses
                  (multiple-value-bind (io s) (load-ref s)
                    (multiple-value-bind (fees s) (load-coins s)
                      (let* ((s (nth-value 1 (load-maybe-ref s)))            ; extra currencies of total_fees
                             (s (nth-value 1 (load-ref s)))                  ; state_update
                             (descr (load-ref s)))
                        (multiple-value-bind (in-cell out-cells) (transaction-messages cell)
                          (declare (ignore io))
                          (let* ((ds (cell-slice descr))
                                 (storage (let ((tag (load-uint ds 4)))
                                            ;; trans_ord$0000 credit_first:Bool storage_ph:(Maybe TrStoragePhase)
                                            (if (= tag 0)
                                                (let ((x (skip-bits ds 5)))
                                                  (multiple-value-bind (has x) (load-bit x)
                                                    (if has (load-coins x) 0)))
                                                0))))
                            (let* ((out-json (mapcar #'%message-json out-cells))
                                   (fees (+ fees (loop for m in out-json
                                                       sum (+ (parse-integer (json-get m "fwd_fee"))
                                                              (parse-integer (json-get m "ihr_fee")))))))
                            (%json-table "@type" "raw.transaction"
                                         "address" (%json-table "@type" "accountAddress" "account_address" (%friendly addr))
                                         "utime" now
                                         "data" (cell->base64 cell)
                                         "transaction_id" (%json-table "@type" "internal.transactionId"
                                                                       "lt" (format nil "~D" lt)
                                                                       "hash" (base64-encode (node-hash-at cell 0)))
                                         "fee" (format nil "~D" fees)
                                         "storage_fee" (format nil "~D" storage)
                                         "other_fee" (format nil "~D" (- fees storage))
                                         "in_msg" (if in-cell (%message-json in-cell) (make-hash-table :test 'equal))
                                         "out_msgs" out-json))))))))))))))))

(defun lite-backend-transactions (lc addr &key from-lt from-hash)
  "As TONLIB-TRANSACTIONS: raw.transaction documents newest first, from the given transaction id
(default: the account's latest), each proved by the hash chain from the account's proved state."
  (let ((count 16))
    (if (and from-lt from-hash)
        (let* ((trusted (lite-sync lc))
               (result (verify-transaction-list
                        (lite-call lc (tl-make "liteServer.getTransactions" :count count :account (%lite-account-id addr)
                                                                            :lt from-lt :hash (base64-decode from-hash)))
                        addr from-lt (base64-decode from-hash) :count count)))
          (declare (ignore trusted))
          (mapcar (lambda (tx) (%transaction-json addr (getf tx :cell))) (getf result :transactions)))
        (let ((r (lite-transactions lc addr :count count)))
          (mapcar (lambda (tx) (%transaction-json addr (getf tx :cell))) (getf r :transactions))))))

(defun lite-backend-shards (lc block &key timeout)
  "As TONLIB-SHARDS: the workchain shard blocks (ton.blockIdExt JSON) the masterchain block BLOCK names.
BLOCK is the newest proved head, or an older masterchain block, which is first proved from it."
  (declare (ignore timeout))
  (let* ((id (json->lite-block-id block))
         (head (lite-sync lc)))
    (unless (%same-block-id-p id head) (lite-prove-block lc id))
    (let ((answer (lite-call lc (tl-make "liteServer.getAllShardsInfo" :id id))))
      (mapcar (lambda (s) (lite-block-id->json
                           (tl-block-id-ext :workchain (getf s :workchain) :shard (getf s :shard) :seqno (getf s :seqno)
                                            :root-hash (getf s :root-hash) :file-hash (getf s :file-hash))))
              (getf (verify-all-shards-info answer id) :shards)))))

(defun %lite-trust-block (lc id)
  "Make sure the block ID (a blockIdExt) is one of the trusted chain: the head's masterchain block, one of
the head's shard blocks, or (proved by a block lookup) any other."
  (let ((head (lite-sync lc)))
    (or (%same-block-id-p id head)
        (and (/= (tl-get id :workchain) -1)
             (let ((answer (lite-call lc (tl-make "liteServer.getAllShardsInfo" :id head))))
               (some (lambda (s) (and (= (getf s :seqno) (tl-get id :seqno))
                                      (equalp (getf s :root-hash) (tl-get id :root-hash))
                                      (equalp (getf s :file-hash) (tl-get id :file-hash))
                                      (= (getf s :workchain) (tl-get id :workchain))
                                      (= (ldb (byte 64 0) (getf s :shard)) (ldb (byte 64 0) (tl-get id :shard)))))
                     (getf (verify-all-shards-info answer head) :shards))))
        (let ((found (getf (lite-lookup-block lc (tl-get id :workchain) (ldb (byte 64 0) (tl-get id :shard))
                                              :seqno (tl-get id :seqno))
                           :block-id)))
          (and found (%same-block-id-p found id)))
        (ton-error "block ~D of workchain ~D is not part of the chain this client trusts"
                   (tl-get id :seqno) (tl-get id :workchain)))))

(defun lite-backend-block-transactions (lc block &key (count 40) timeout)
  "As TONLIB-BLOCK-TRANSACTIONS: up to COUNT short transaction ids (blocks.shortTxId JSON) of a block, NIL COUNT
following the pagination to the end.  Each is proved to be in the block."
  (declare (ignore timeout))
  (let ((id (json->lite-block-id block)))
    (%lite-trust-block lc id)
    (collect-block-transactions
     (lambda (request)
       (let* ((mode (getf request :|mode|))
              (after (getf request :|after|))
              (req (apply #'tl-make "liteServer.listBlockTransactions"
                          :id id :mode (logior mode 32) :count (getf request :|count|)
                          (and after (list :after (tl-make "liteServer.transactionId3"
                                                           :account (base64-decode (getf after :|account|))
                                                           :lt (let ((l (getf after :|lt|))) (if (stringp l) (parse-integer l) l)))))))
              (result (verify-block-transactions (lite-call lc req) id :count (getf request :|count|))))
         (%json-table "@type" "blocks.transactions"
                      "incomplete" (getf result :incomplete)
                      "transactions"
                      (mapcar (lambda (tx)
                                (%json-table "@type" "blocks.shortTxId"
                                             "mode" mode
                                             "account" (base64-encode (getf tx :account))
                                             "lt" (format nil "~D" (getf tx :lt))
                                             "hash" (base64-encode (getf tx :hash))))
                              (getf result :transactions)))))
     id count)))

;;; --- opening a lite client from a global config ------------------------------------------------------

(defun %config-block-id (json)
  (let ((shard (json-get json "shard")))
    (tl-block-id-ext :workchain (json-get json "workchain")
                     :shard (if (stringp shard) (parse-integer shard) shard)
                     :seqno (json-get json "seqno")
                     :root-hash (base64-decode (json-get json "root_hash"))
                     :file-hash (base64-decode (json-get json "file_hash")))))

(defun open-lite-backend (config-text &key state-file name)
  "A lite client (see LITE-BACKEND-* above) for the FIRST liteserver of the global config CONFIG-TEXT -- in
the application the single entry the local proxy-liteserver writes -- trusting what tonlib trusts:
validator.init_block when the config has one (a key block), else validator.zero_state.  STATE-FILE keeps
the proved key block between runs (see OPEN-LITE-CLIENT)."
  (let* ((doc (json-decode config-text))
         (entry (let ((l (json-get doc "liteservers"))) (and (consp l) (first l))))
         (validator (json-get doc "validator"))
         (init (and (hash-table-p validator) (json-get validator "init_block")))
         (zero (and (hash-table-p validator) (json-get validator "zero_state")))
         (anchor (cond ((and (hash-table-p init) (plusp (or (json-get init "seqno") 0))) (%config-block-id init))
                       ((hash-table-p zero) (%config-block-id zero))
                       (t (ton-error "the global config has neither validator.init_block nor validator.zero_state")))))
    (unless (hash-table-p entry) (ton-error "the global config lists no liteserver"))
    (let* ((ip (ldb (byte 32 0) (json-get entry "ip")))
           (host (format nil "~D.~D.~D.~D" (ldb (byte 8 24) ip) (ldb (byte 8 16) ip) (ldb (byte 8 8) ip) (ldb (byte 8 0) ip)))
           (public (base64-decode (json-get (json-get entry "id") "key"))))
      (open-lite-client host (json-get entry "port") public anchor :name name :state-file state-file :head-slack 150))))

;;; --- the real-network check of the lite backend ------------------------------------------------------

(defparameter *diagnose-lite-getter* "active_election_id"
  "The getter DIAGNOSE-LITE runs on the default account (the elector contract).")

;;; --- real links kept as test vectors ---------------------------------------------------------------

(defun save-link-vector (vector directory)
  "Write VECTOR (a plist of PROOF-SINGLE-LINKS) into DIRECTORY as link-<kind>-<from>-<to>.bin (the TL encoding
of the one-link proof) and .sexp (the start block, the kind).  The link is verified first -- from the start
block alone, counting its signature set -- and must be of the kind it says.  Returns the .bin path."
  (let* ((known (getf vector :known)) (proof (getf vector :proof)) (kind (getf vector :kind))
         (counts (list :ordinary 0 :simplex 0))
         (result (let ((*signature-set-counts* counts)) (verify-partial-block-proof proof known)))
         (name (format nil "link-~(~A~)-~D-~D" kind (getf vector :from-seqno) (getf vector :to-seqno)))
         (bin (merge-pathnames (format nil "~A.bin" name) (uiop:ensure-directory-pathname directory)))
         (sexp (merge-pathnames (format nil "~A.sexp" name) bin)))
    (unless (and (= 1 (getf result :steps)) (= 1 (getf counts kind)))
      (ton-error "link ~D -> ~D does not verify alone as a ~(~A~) link" (getf vector :from-seqno) (getf vector :to-seqno) kind))
    (ensure-directories-exist bin)
    (with-open-file (o bin :direction :output :if-exists :supersede :element-type '(unsigned-byte 8))
      (write-sequence (tl-encode proof) o))
    (with-open-file (o sexp :direction :output :if-exists :supersede)
      (with-standard-io-syntax
        (let ((*print-pretty* nil))
          (prin1 (list :kind kind :from-seqno (getf vector :from-seqno) :to-seqno (getf vector :to-seqno)
                       :known (list :workchain (tl-get known :workchain) :shard (tl-get known :shard) :seqno (tl-get known :seqno)
                                    :root-hash (octets->hex (tl-get known :root-hash)) :file-hash (octets->hex (tl-get known :file-hash))))
                 o))))
    bin))

(defun load-link-vector (bin)
  "(VALUES KNOWN PROOF META) of a file written by SAVE-LINK-VECTOR: the start block as a blockIdExt, the decoded
one-link proof, and the .sexp plist."
  (let* ((meta (with-open-file (i (make-pathname :type "sexp" :defaults bin))
                 (with-standard-io-syntax (let ((*read-eval* nil)) (read i)))))
         (k (getf meta :known))
         (bytes (with-open-file (i bin :element-type '(unsigned-byte 8))
                  (let ((v (make-array (file-length i) :element-type '(unsigned-byte 8)))) (read-sequence v i) v))))
    (values (tl-block-id-ext :workchain (getf k :workchain) :shard (getf k :shard) :seqno (getf k :seqno)
                             :root-hash (hex->octets (getf k :root-hash)) :file-hash (hex->octets (getf k :file-hash)))
            (tl-decode bytes)
            meta)))

(defun make-link-capture () (make-hash-table))

(defun link-capture-note (table proof)
  "Remember, from PROOF, the first and the last Simplex link and the last ordinary link of a key-block walk."
  (dolist (v (proof-single-links proof))
    (ecase (getf v :kind)
      (:simplex (unless (gethash :first-simplex table) (setf (gethash :first-simplex table) v))
                (setf (gethash :last-simplex table) v))
      (:ordinary (setf (gethash :last-ordinary table) v)))))

(defun write-link-captures (table directory)
  "Save what LINK-CAPTURE-NOTE kept into DIRECTORY; returns the file names (a link kept twice is saved once)."
  (let ((saved '()))
    (dolist (key '(:first-simplex :last-simplex :last-ordinary))
      (let ((v (gethash key table)))
        (when v (pushnew (file-namestring (save-link-vector v directory)) saved :test #'string=))))
    (nreverse saved)))

(defun diagnose-lite (global-config &key (timeout 25) db keystore (sync-total-timeout 900) (stream *standard-output*)
                                      (account *diagnose-account*) (getter *diagnose-lite-getter*)
                                      (verify-vset-hash t))
  "The check of the LITE BACKEND against a real network: start the native proxy on GLOBAL-CONFIG (a path),
open the lite client THROUGH it, walk the block-proof chain from the config's init block to the newest key
block (patiently, up to SYNC-TOTAL-TIMEOUT seconds, printing the progress; the proved key block is kept in
KEYSTORE so a second run is quick), then exercise every call the application makes -- masterchain info,
account state, a getter, the configuration, the shards, the transactions of a block, an account's
transactions, a proof of an older block, a block lookup by time -- each timed.  Prints a report ending
in RESULT: OK or FAILED, and returns (VALUES OK-P REPORT-STRING).  With VERIFY-VSET-HASH NIL the
validator-set hash check of key-block links is switched off (to tell whether it is what refuses real links)."
  (let* ((scratch (not db))
         (db (or db (format nil "~A/ton-trader-diagnose-lite-~D-~D/"
                            (string-right-trim "/" (namestring (uiop:temporary-directory)))
                            (sb-posix:getpid) (get-universal-time))))
         (proxy nil) (lc nil) (lines '()) (ok t))
    (flet ((say (control &rest args)
             (when stream
               (sb-thread:with-recursive-lock (*adnl-log-lock*)
                 (format stream "~&[~A] ~?~%" (%utc-hms (get-universal-time)) control args)
                 (finish-output stream))))
           (secs (since) (/ (- (get-internal-real-time) since) (float internal-time-units-per-second))))
      (let ((*verify-validator-set-hash* verify-vset-hash)
            (*signature-set-counts* (list :ordinary 0 :simplex 0)))
        (unwind-protect
             (progn
               (setf proxy (open-proxy-liteserver :implementation :native :global-config global-config :db db :port 0
                                                  :log (lambda (control &rest args) (declare (ignore control args)))))
               (if (not (proxy-wait-ready proxy :timeout timeout))
                   (progn (setf ok nil)
                          (push (format nil "the proxy found no upstream within ~Ds: ~A" timeout (proxy-verdict proxy)) lines))
                   (let ((routed (proxy-liteserver-global-config-path
                                  proxy global-config (format nil "~Alite-diagnose.global.json" (uiop:ensure-directory-pathname db)))))
                     (macrolet ((diag-step ((name) &body body)
                                  `(let ((t0 (get-internal-real-time)))
                                     (handler-case
                                         (let ((detail (progn ,@body)))
                                           (push (format nil "ok      ~A (~,1Fs)~@[: ~A~]" ,name (secs t0) detail) lines)
                                           (say "~A: ok" ,name))
                                       (error (e)
                                         (setf ok nil)
                                         (push (format nil "FAILED  ~A (~,1Fs): ~A" ,name (secs t0) e) lines)
                                         (say "~A: FAILED ~A" ,name e))))))
                       (setf lc (open-lite-backend (uiop:read-file-string routed)
                                                   :name "diagnose"
                                                   :state-file (and keystore (merge-pathnames "lite-client.state"
                                                                                              (uiop:ensure-directory-pathname (ensure-keystore keystore))))))
                       (say "lite: anchor block ~D; walking the block-proof chain to the newest key block (minutes on a weak link)..."
                            (tl-get (lite-client-key-block lc) :seqno))
                       (let ((t0 (get-internal-real-time)) (deadline (+ (get-universal-time) sync-total-timeout))
                             (last-key -1) (stalled 0) (synced nil)
                             (captures (make-link-capture))
                             (*lite-proof-hook* nil))
                         (setf *lite-proof-hook* (lambda (proof) (link-capture-note captures proof)))
                         (loop until (or synced (> (get-universal-time) deadline) (>= stalled 3))
                               do (handler-case
                                      (progn (lite-sync lc :progress (lambda (seqno) (say "lite: proved key block ~D" seqno))
                                                    :trace (lambda (line) (say "~A" line)))
                                             (setf synced t))
                                    (error (e) (say "lite: sync attempt did not finish: ~A" e)
                                      (push (format nil "sync attempt: ~A" e) lines)))
                                  (let ((key (tl-get (lite-client-key-block lc) :seqno)))
                                    (if (> key last-key) (setf stalled 0 last-key key) (incf stalled))))
                         (if synced
                             (push (format nil "ok      sync from the init block to key block ~D (~,1Fs); signature sets checked: ~D ordinary, ~D Simplex"
                                           (tl-get (lite-client-key-block lc) :seqno) (secs t0)
                                           (getf *signature-set-counts* :ordinary) (getf *signature-set-counts* :simplex))
                                   lines)
                             (progn (setf ok nil) (push (format nil "FAILED  sync (~,1Fs), key block reached: ~D" (secs t0) last-key) lines)))
                         ;; the real links this walk verified, kept as test vectors (a Simplex one above all)
                         (when synced
                           (handler-case
                               (let* ((dir (merge-pathnames "capture/" (uiop:ensure-directory-pathname
                                                                        (if keystore (ensure-keystore keystore) db))))
                                      (files (write-link-captures captures dir)))
                                 (push (if files
                                           (format nil "ok      real link vectors kept in ~A: ~{~A~^, ~} (send these files)" dir files)
                                           "ok      no link vector captured (the walk resumed from a saved key block)")
                                       lines))
                             (error (e) (push (format nil "note    link vectors not saved: ~A" e) lines)))))
                       (when ok
                         (let ((addr (parse-address account)) head shards)
                           (diag-step ("masterchain head") (setf head (lite-sync lc)) (format nil "seqno ~D" (tl-get head :seqno)))
                           (diag-step ("account state") (let ((st (tonlib-account-state lc addr)))
                                                     (format nil "~(~A~), balance ~D nanoTON" (account-state-status st) (account-state-balance st))))
                           (diag-step ("getter") (multiple-value-bind (items code) (tonlib-run-get-method lc addr getter nil)
                                              (format nil "~A exit ~A, ~D item~:P" getter code (length items))))
                           (diag-step ("configuration") (format nil "dictionary ~A..." (subseq (cell-hash-hex (tonlib-config-cell lc)) 0 12)))
                           (diag-step ("shards of the head")
                             (setf shards (tonlib-shards lc (tonlib-masterchain-block lc)))
                             (format nil "~D shard block~:P" (length shards)))
                           (diag-step ("transactions of a shard block")
                             (let ((n (loop for sh in shards sum (length (tonlib-block-transactions lc sh :count 5)))))
                               (format nil "~D short id~:P in the first ~D shard~:P" n (length shards))))
                           (diag-step ("transactions of the account")
                             (format nil "~D transaction~:P" (length (tonlib-transactions lc addr))))
                           (let (older)
                             (diag-step ("proof of an older masterchain block")
                               (unless head (ton-error "skipped: the masterchain head step failed"))
                               (let* ((seqno (max 2 (- (tl-get head :seqno) 100)))
                                      (found (lite-lookup-block lc -1 (ash 1 63) :seqno seqno)))
                                 (setf older found)
                                 (lite-prove-block lc (getf found :block-id))
                                 (format nil "block ~D" seqno)))
                             (diag-step ("block lookup by time")
                               (unless older (ton-error "skipped: the step before found no older block"))
                               (let* ((utime (getf (getf older :info) :gen-utime))
                                      (b (lite-lookup-block lc -1 (ash 1 63) :utime utime)))
                                 (format nil "time ~D -> block ~D (the older block is ~D)" utime
                                         (tl-get (getf b :block-id) :seqno) (tl-get (getf older :block-id) :seqno))))))))))
               (let ((report (with-output-to-string (o)
                               (when proxy (write-string (proxy-diagnostics-report proxy) o))
                               (dolist (l (reverse lines)) (format o "~A~%" l))
                               (format o "~A~%" (ironclad-assembly-line))
                               (format o "RESULT: ~A~%" (if ok "OK" "FAILED")))))
                 (when stream (format stream "~&~A" report) (finish-output stream))
                 (return-from diagnose-lite (values ok report))))
          (ignore-errors (when lc (close-lite-client lc)))
          (ignore-errors (when proxy (close-proxy-liteserver proxy)))
          (when scratch (ignore-errors (uiop:delete-directory-tree (uiop:ensure-directory-pathname db)
                                                                   :validate t :if-does-not-exist :ignore))))))))
