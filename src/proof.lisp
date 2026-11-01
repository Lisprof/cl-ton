;;;; proof.lisp -- the proof an answer was verified against, as a typed TL object (clton.Proof, tests/tl/cl_ton_api.tl).
;;;;
;;;; The lite client verifies every liteserver answer (proof-verify.lisp) and used to keep only the verified values.  A
;;;; PROOF keeps what was verified -- the answer as received and the trusted masterchain block id -- so that the typed
;;;; answers of TONLIB-EXECUTE carry it, a consumer can check it again with VERIFY-PROOF, and it can be sent as TL bytes.

(in-package :cl-ton)

(defun make-account-state-proof (trusted address answer)
  "The clton.proofAccountState for the liteServer.accountState ANSWER about ADDRESS, proved against the masterchain block
id TRUSTED (a blockIdExt tl-obj)."
  (tl-make "clton.proofAccountState"
           :trusted trusted
           :workchain (address-workchain address)
           :account (address-hash address)
           :answer answer))

(defun make-all-shards-proof (block-id answer)
  "The clton.proofAllShards for the liteServer.allShardsInfo ANSWER about the masterchain block BLOCK-ID (a proved one)."
  (tl-make "clton.proofAllShards" :block block-id :answer answer))

(defun make-config-proof (trusted answer)
  "The clton.proofConfig for the liteServer.configInfo ANSWER (the whole configuration), proved against TRUSTED."
  (tl-make "clton.proofConfig" :trusted trusted :answer answer))

;;; Transactions of an account: the list is chained, by hashes, to the transaction (LT, HASH) it starts from.  When that start
;;; is the account's LATEST transaction, it comes from the proved account state and STATES holds that account-state proof
;;; (one element); when the caller named the start, STATES is empty and the start is the caller's.
(defun make-transactions-proof (address lt hash count states answer)
  "The clton.proofTransactions for the liteServer.transactionList ANSWER about ADDRESS, asked for up to COUNT transactions
from (LT, HASH); STATES is a list of the clton.proofAccountState the start comes from, or NIL."
  (tl-make "clton.proofTransactions"
           :workchain (address-workchain address)
           :account (address-hash address)
           :lt lt :hash hash :count count
           :states (coerce states 'vector)
           :answer answer))

(defun make-block-transactions-proof (block-id reverse pages)
  "The clton.proofBlockTransactions for the transactions of BLOCK-ID (a blockIdExt tl-obj the caller trusts): PAGES is a
list of (COUNT . liteServer.blockTransactions answer), COUNT the number of transactions that page asked for."
  (tl-make "clton.proofBlockTransactions"
           :block block-id
           :reverse (and reverse t)
           :pages (coerce (mapcar (lambda (page)
                                    (tl-make "clton.blockTransactionsPage" :count (car page) :answer (cdr page)))
                                  pages)
                          'vector)))

(defun %verify-transactions-proof (proof)
  (let* ((address (make-address :workchain (tl-get proof :workchain) :hash (tl-get proof :account)))
         (lt (tl-get proof :lt))
         (hash (tl-get proof :hash))
         (states (coerce (tl-get proof :states) 'list)))
    (when states
      (%prove (= 1 (length states)) "~D account states in a transactions proof" (length states))
      (let ((state (verify-proof (first states))))
        (%prove (and (getf state :exists)
                     (= lt (getf state :last-trans-lt))
                     (equalp hash (getf state :last-trans-hash)))
                "the proved state of the account does not end in the transaction the list starts from")))
    (verify-transaction-list (tl-get proof :answer) address lt hash :count (tl-get proof :count))))

(defun %verify-block-transactions-proof (proof)
  (let ((block (tl-get proof :block))
        (transactions '())
        (incomplete nil))
    (loop for page across (tl-get proof :pages)
          do (let ((result (verify-block-transactions (tl-get page :answer) block
                                                      :count (tl-get page :count) :reverse (tl-get proof :reverse))))
               (setf transactions (append transactions (getf result :transactions))
                     incomplete (getf result :incomplete))))
    (list :transactions transactions :incomplete incomplete)))

;;; A getter run: the emulator ran on an account state, a configuration and some libraries; this proves the INPUTS (the run itself
;;; is deterministic and local: re-run it with RUN-ACCOUNT-GET-METHOD on what VERIFY-PROOF returns).  A library is named by its
;;; own hash, so the BoC of each one proves itself.
(defun make-run-proof (state-proof config-proof libraries)
  "The clton.proofRunMethod of a getter run on the account state STATE-PROOF (a clton.proofAccountState), with the configuration
CONFIG-PROOF (a clton.proofConfig) and LIBRARIES, an alist of (hash-hex . cell)."
  (tl-make "clton.proofRunMethod"
           :state state-proof :config config-proof
           :libraries (coerce (mapcar (lambda (entry) (serialize-boc (cdr entry))) libraries) 'vector)))

(defun %verify-run-proof (proof)
  (let ((state (verify-proof (tl-get proof :state)))
        (config (verify-proof (tl-get proof :config))))
    (list :account-cell (getf state :account-cell)
          :config-root (getf config :config-root)
          :libraries (loop for octets across (tl-get proof :libraries)
                           collect (let ((cell (first (parse-boc octets))))
                                     (cons (cell-hash-hex cell) cell))))))

(defun proof-p (object)
  (and (tl-obj-p object)
       (let ((name (tl-obj-name object)))
         (and (> (length name) 11) (string= "clton.proof" name :end2 11)))))

(defun proof-trusted-block (proof)
  "The block id (a blockIdExt tl-obj) PROOF was verified against: the masterchain block for the state, shard and configuration
proofs (for a list of transactions that starts from the account's latest one, the block its account state was proved at,
NIL when the caller named the start), the block itself for the transactions of a block."
  (or (tl-get proof :trusted) (tl-get proof :block)
      (let ((state (cond ((tl-is proof "clton.proofTransactions") (find-if #'identity (tl-get proof :states)))
                         ((tl-is proof "clton.proofRunMethod") (tl-get proof :state)))))
        (and state (proof-trusted-block state)))))

(defun verify-proof (proof)
  "Check PROOF again, from the answer it holds and the trusted block it names: the plist the verifier returns (for an
account state: :EXISTS :ACCOUNT-CELL :LAST-TRANS-LT :LAST-TRANS-HASH :SHARD-BLOCK :STATE-HASH; for the shards: :SHARDS; for
the configuration: :CONFIG-ROOT), or a PROOF-ERROR when it does not hold."
  (cond ((tl-is proof "clton.proofAccountState")
         (verify-account-state (tl-get proof :answer)
                               (make-address :workchain (tl-get proof :workchain) :hash (tl-get proof :account))
                               (tl-get proof :trusted)))
        ((tl-is proof "clton.proofAllShards")
         (verify-all-shards-info (tl-get proof :answer) (tl-get proof :block)))
        ((tl-is proof "clton.proofConfig")
         (verify-config-info (tl-get proof :answer) (tl-get proof :trusted) :all t))
        ((tl-is proof "clton.proofTransactions")
         (with-proof-errors (%verify-transactions-proof proof)))
        ((tl-is proof "clton.proofBlockTransactions")
         (with-proof-errors (%verify-block-transactions-proof proof)))
        ((tl-is proof "clton.proofRunMethod")
         (with-proof-errors (%verify-run-proof proof)))
        (t (ton-error "not a proof: ~S" proof))))

(defun proof->octets (proof)
  "PROOF as TL bytes."
  (unless (proof-p proof) (ton-error "not a proof: ~S" proof))
  (tl-encode proof))

(defun octets->proof (octets)
  "The proof the TL bytes OCTETS encode; signals when they encode something else."
  (let ((object (tl-decode octets)))
    (unless (proof-p object) (ton-error "not a proof: ~S" object))
    object))
