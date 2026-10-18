;;;; proof-verify.lisp -- check what a liteserver says, from a trusted block hash downwards.
;;;;
;;;; A liteserver is not trusted.  What it answers about an account is believed only after a chain
;;;; of Merkle proofs leads from a block hash the client already trusts to the account cell:
;;;;
;;;;   trusted masterchain block hash
;;;;     -> its block proof (a Merkle proof of the block header)       VERIFY-BLOCK-PROOF
;;;;     -> the block's state_update names the masterchain state hash
;;;;     -> the state proof (a Merkle proof of that state)
;;;;     -> shard_hashes: the shard that holds the account, with its block's seqno and hashes
;;;;   shard block (hashes now vouched for)
;;;;     -> its block proof, its state_update, its state proof          (the same two steps)
;;;;     -> the accounts dictionary, looked up by the account hash      DICT-LOOKUP
;;;;     -> the ShardAccount, whose account cell must be the served state
;;;;
;;;; Every step reads data only out of cells the proofs reveal: CELL-SLICE refuses a pruned branch,
;;;; so a lookup that wanders into a pruned subtree is an error, never a silent misread.  Every
;;;; failed comparison signals a PROOF-ERROR saying which one.

(in-package :cl-ton)

(define-condition proof-error (ton-error) ()
  (:documentation "A liteserver answer that does not verify."))

(defmacro with-proof-errors (&body body)
  "Run BODY; any TON-ERROR or BOC-ERROR from reading the answer (a malformed BOC, a read into a
pruned cell, a short slice) is reported as a PROOF-ERROR: whatever the cause, the answer does not
verify.  Other kinds of error are not caught: they would be bugs, and the fuzz tests look for them."
  `(handler-case (progn ,@body)
     (proof-error (e) (error e))
     ((or ton-error boc-error) (e)
       (error 'proof-error :format-control "malformed proof data: ~A" :format-arguments (list e)))))

(defmacro define-proof-function (name lambda-list &body body)
  "DEFUN whose body runs under WITH-PROOF-ERRORS: a reader of proof data signals a PROOF-ERROR
for any malformed cell, whether it is called by a verifier or directly."
  (let ((doc (when (and (stringp (first body)) (rest body)) (pop body))))
    `(defun ,name ,lambda-list ,@(and doc (list doc)) (with-proof-errors ,@body))))

(defmacro %prove (test control &rest arguments)
  "Signal a PROOF-ERROR unless TEST: a verification step reads as the fact it establishes."
  `(unless ,test (error 'proof-error :format-control ,control :format-arguments (list ,@arguments))))

;;; --- dictionaries -----------------------------------------------------------------

(define-proof-function dict-lookup-in-slice (slice key key-bits)
  "DICT-LOOKUP for a Hashmap/HashmapAug whose root edge is the rest of SLICE, as when the dictionary is
stored inline in a larger cell (the transactions of an AccountBlock): its children are the next two
references of SLICE.  (VALUES SLICE FOUND-P) as DICT-LOOKUP."
  (let ((current slice) (consumed 0))
    (loop
      (let ((m (- key-bits consumed)))
        (multiple-value-bind (label n rest) (load-hm-label current m)
          (%prove (<= n m) "dictionary label of ~D bits longer than the ~D left of the key" n m)
          (unless (= label (ldb (byte n (- m n)) key))
            (return (values nil nil)))
          (when (= n m)
            (return (values rest t)))
          (multiple-value-bind (left rest2) (load-ref rest)
            (let ((right (load-ref rest2)))
              (setf current (cell-slice (if (zerop (ldb (byte 1 (- m n 1)) key)) left right))
                    consumed (+ consumed n 1)))))))))

(define-proof-function dict-lookup (root key key-bits)
  "Look KEY (an integer of KEY-BITS bits) up in the Hashmap/HashmapAug whose root edge cell is
ROOT (NIL for an empty one).  (VALUES SLICE FOUND-P): SLICE is positioned after the leaf's label
(for an augmented map the extra comes first), FOUND-P false when the proof shows KEY absent.
Signals if the path runs into a pruned cell."
  (if (null root)
      (values nil nil)
      (dict-lookup-in-slice (cell-slice root) key key-bits)))

;;; --- blocks -----------------------------------------------------------------------

(defun %fetch-hash (s) (load-bytes s 32))

(defun %shard-id (pfx-bits prefix)
  "The 64-bit shard id of a ShardIdent: its prefix with the terminating 1 bit put back at position
63-PFX-BITS (the wire form clears it, so a whole workchain is prefix 0).  Refuses what
ShardIdent::is_valid refuses: more than 60 prefix bits, or bits set beyond the prefix."
  (%prove (<= pfx-bits 60) "a shard prefix of ~D bits (at most 60)" pfx-bits)
  (%prove (zerop (ldb (byte (- 64 pfx-bits) 0) prefix)) "a shard prefix has bits set beyond its ~D" pfx-bits)
  (logior prefix (ash 1 (- 63 pfx-bits))))

(define-proof-function parse-block-info (info)
  "The BlockInfo fields a client binds a block id to: (:SEQNO :WORKCHAIN :SHARD :SHARD-PREFIX-BITS
:KEY-BLOCK :GEN-UTIME :START-LT :END-LT :VALIDATOR-LIST-HASH :CATCHAIN-SEQNO).
block_info#9bc7a987 version:uint32 not_master:(## 1) after_merge:(## 1) before_split:(## 1)
after_split:(## 1) want_split:Bool want_merge:Bool key_block:Bool vert_seqno_incr:(## 1) flags:(## 8)
seq_no:# vert_seq_no:# shard:ShardIdent gen_utime:uint32 start_lt:uint64 end_lt:uint64\ngen_validator_list_hash_short:uint32 gen_catchain_seqno:uint32 ..."
  (let ((s (cell-slice info)))
    (%prove (= (load-uint s 32) #x9bc7a987) "not a BlockInfo cell")
    (let ((s (skip-bits s 64)))                 ; tag, version
      (let ((s (skip-bits s 6)))                ; not_master after_merge before_split after_split want_split want_merge
        (multiple-value-bind (key-block s) (load-uint s 1)
          (let ((s (skip-bits s 9)))            ; vert_seqno_incr, flags
            (multiple-value-bind (seqno s) (load-uint s 32)
              (let ((s (skip-bits s 32)))       ; vert_seq_no
                (multiple-value-bind (tag s) (load-uint s 2)
                  (%prove (zerop tag) "unexpected ShardIdent constructor ~D" tag)
                  (multiple-value-bind (pfx-bits s) (load-uint s 6)
                    (multiple-value-bind (workchain s) (load-int s 32)
                      (multiple-value-bind (prefix s) (load-uint s 64)
                        (multiple-value-bind (utime s) (load-uint s 32)
                          (multiple-value-bind (start-lt s) (load-uint s 64)
                            (multiple-value-bind (end-lt s) (load-uint s 64)
                              (multiple-value-bind (list-hash s) (load-uint s 32)
                                (list :seqno seqno :workchain workchain :shard (%shard-id pfx-bits prefix)
                                      :shard-prefix-bits pfx-bits :key-block (= key-block 1)
                                      :gen-utime utime :start-lt start-lt :end-lt end-lt
                                      :validator-list-hash list-hash :catchain-seqno (load-uint s 32))))))))))))))))))

(defun verify-block-proof (proof block-id &key (check-info t) (require-update t))
  "PROOF, the Merkle proof cell of a block header, against BLOCK-ID (a blockIdExt tl-obj, or an
whatever answers TL-GET for :root-hash :workchain :shard :seqno).  (VALUES BLOCK STATE-HASH INFO): the
revealed block cell, the hash its state_update says the resulting state has, and the parsed
BlockInfo.  Checks, in order: the proof is of the block hash BLOCK-ID names; the block has the
block constructor and a Merkle update as its state_update; BlockInfo agrees with BLOCK-ID.  A node's forward link reveals only the block root and BlockInfo
(liteserver.cpp reads nothing else), so its state_update is a pruned branch: with REQUIRE-UPDATE nil that
is accepted and STATE-HASH is NIL."
  (let* ((expected (tl-get block-id :root-hash))
         (block (handler-case (verify-merkle-proof proof expected)
                  (boc-error (e) (%prove nil "block proof: ~A" e)))))
    (%prove (and (cell-p block) (not (cell-exotic-p block))) "block proof: the block is not an ordinary cell")
    (let ((s (cell-slice block)))
      (%prove (= (load-uint s 32) #x11ef55aa) "block proof: not a Block cell"))
    (%prove (= 4 (length (cell-refs block))) "block proof: a Block has four references")
    (let* ((update (svref (cell-refs block) 2))
           (info (parse-block-info (svref (cell-refs block) 0))))
      (%prove (and (cell-p update)
                   (or (eql 4 (cell-special-type update))
                       (and (not require-update) (pruned-branch-p update))))
              "block proof: state_update is not a Merkle update")
      (when check-info
        (%prove (= (getf info :seqno) (tl-get block-id :seqno)) "block proof: BlockInfo seqno ~D, block id ~D"
                (getf info :seqno) (tl-get block-id :seqno))
        (%prove (= (getf info :workchain) (tl-get block-id :workchain)) "block proof: BlockInfo workchain differs")
        (%prove (= (getf info :shard) (ldb (byte 64 0) (tl-get block-id :shard))) "block proof: BlockInfo shard differs"))
      (values block (and (eql 4 (cell-special-type update)) (nth-value 1 (merkle-update-hashes update))) info))))

;;; --- states -----------------------------------------------------------------------

(define-proof-function parse-shard-state-header (state)
  "The fields of a ShardStateUnsplit cell a client needs: (:WORKCHAIN :SHARD :SEQNO :GEN-UTIME :GEN-LT
:ACCOUNTS :CUSTOM), ACCOUNTS the ShardAccounts cell, CUSTOM the McStateExtra cell or NIL.
shard_state#9023afe2 global_id:int32 shard_id:ShardIdent seq_no:uint32 vert_seq_no:# gen_utime:uint32
gen_lt:uint64 min_ref_mc_seqno:uint32 out_msg_queue_info:^... before_split:(## 1) accounts:^ShardAccounts
^[...] custom:(Maybe ^McStateExtra): the references come in that order."
  (let ((s (cell-slice state)) (refs (cell-refs state)))
    (%prove (= (load-uint s 32) #x9023afe2) "state: not a ShardStateUnsplit")
    (let ((s (skip-bits s 64)))                 ; tag, global_id
      (multiple-value-bind (tag s) (load-uint s 2)
        (%prove (zerop tag) "state: unexpected ShardIdent constructor ~D" tag)
        (multiple-value-bind (pfx-bits s) (load-uint s 6)
         (multiple-value-bind (workchain s) (load-int s 32)
          (multiple-value-bind (prefix s) (load-uint s 64)
            (multiple-value-bind (seqno s) (load-uint s 32)
              (multiple-value-bind (utime s) (load-uint (skip-bits s 32) 32) ; vert_seq_no
                (%prove (>= (length refs) 3) "state: too few references (~D)" (length refs))
                (list :workchain workchain :shard (%shard-id pfx-bits prefix) :seqno seqno :gen-utime utime
                      :gen-lt (load-uint s 64)
                      :accounts (svref refs 1)
                      :custom (and (= 4 (length refs)) (svref refs 3))))))))))))

(define-proof-function find-shard-description (mc-state workchain account-hash)
  "The ShardDescr prefix (:SEQNO :ROOT-HASH :FILE-HASH :SHARD) of the shard of WORKCHAIN that
holds ACCOUNT-HASH (an integer), from the masterchain state MC-STATE's shard_hashes."
  (let* ((header (parse-shard-state-header mc-state))
         (custom (getf header :custom)))
    (%prove custom "masterchain state has no McStateExtra")
    (let ((s (cell-slice custom)))
      (%prove (= (load-uint s 16) #xcc26) "masterchain state: not a McStateExtra")
      (let* ((s (skip-bits s 16))
             (dict-root (load-maybe-ref s)))
        (multiple-value-bind (value found) (dict-lookup dict-root (ldb (byte 32 0) workchain) 32)
          (%prove found "masterchain state lists no shards of workchain ~D" workchain)
          ;; value: ^(BinTree ShardDescr); descend by the account's high bits
          (let ((cell (load-ref value)) (depth 0) (prefix 0))
            (loop
              (let ((ts (cell-slice cell)))
                (if (zerop (load-uint ts 1))
                    (let ((d (skip-bits ts 1)))
                      (multiple-value-bind (tag d) (load-uint d 4)
                        (%prove (member tag '(#xa #xb)) "unexpected ShardDescr constructor ~D" tag)
                        (multiple-value-bind (seqno d) (load-uint d 32)
                          (let ((d (skip-bits d 32)))   ; reg_mc_seqno
                            (let ((d (skip-bits d 128))) ; start_lt end_lt
                              (multiple-value-bind (root-hash d) (%fetch-hash d)
                                (let ((file-hash (%fetch-hash d)))
                                  (return (list :seqno seqno :root-hash root-hash :file-hash file-hash
                                                :shard (logior (ash prefix (- 64 depth)) (ash 1 (- 63 depth)))
                                                :depth depth)))))))))
                    (progn
                      (%prove (< depth 60) "shard tree deeper than 60 levels")
                      (multiple-value-bind (left s2) (load-ref (skip-bits ts 1))
                        (let ((right (load-ref s2))
                              (bit (ldb (byte 1 (- 255 depth)) account-hash)))
                          (setf cell (if (zerop bit) left right)
                                prefix (logior (ash prefix 1) bit))
                          (incf depth)))))))))))))

;;; --- an account -----------------------------------------------------------------------

(defun %verified-state (proof-roots block-id what)
  "PROOF-ROOTS, the two cells (block proof, state proof) of a proof BOC: (VALUES STATE BLOCK INFO) after
verifying the block proof against BLOCK-ID and the state proof against the state hash the block names."
  (%prove (= 2 (length proof-roots)) "~A proof: expected a block proof and a state proof, got ~D roots"
          what (length proof-roots))
  (multiple-value-bind (block state-hash info)
      (verify-block-proof (first proof-roots) block-id)
    (let ((state (handler-case (verify-merkle-proof (second proof-roots) state-hash)
                   (boc-error (e) (%prove nil "~A state proof: ~A" what e)))))
      (values state block info))))

(defun verify-account-state (answer account trusted-mc-block)
  (with-proof-errors (%verify-account-state answer account trusted-mc-block)))

(defun %verify-account-state (answer account trusted-mc-block)
  "ANSWER, a decoded liteServer.accountState (:ID :SHARDBLK :SHARD-PROOF :PROOF :STATE), as the
answer about ACCOUNT (an ADDRESS) at the masterchain block TRUSTED-MC-BLOCK (a blockIdExt tl-obj
the caller trusts: it is the one thing not proved here).  Returns a plist (:EXISTS :ACCOUNT-CELL
:LAST-TRANS-LT :LAST-TRANS-HASH :SHARD-BLOCK :STATE-HASH) or signals a PROOF-ERROR.  An account the
proof shows absent must come with an empty state, and one it shows present with exactly its
account cell."
  (let* ((workchain (address-workchain account))
         (account-int (octets->uint (address-hash account)))
         (answered-id (tl-get answer :id))
         (shardblk (tl-get answer :shardblk)))
    (%prove-same-block-id answered-id trusted-mc-block "account state")
    (%prove (= (tl-get shardblk :workchain) workchain) "the answer's shard block is of workchain ~D, not ~D"
            (tl-get shardblk :workchain) workchain)
    (if (= workchain -1)
        (%prove (and (equalp (tl-get shardblk :root-hash) (tl-get trusted-mc-block :root-hash))
                     (zerop (length (tl-get answer :shard-proof))))
                "a masterchain account is proved in the masterchain block itself, with no shard proof")
        ;; the masterchain says which shard block holds the account
        (let ((mc-roots (parse-boc (tl-get answer :shard-proof))))
          (multiple-value-bind (mc-state) (%verified-state mc-roots trusted-mc-block "shard")
            (let ((descr (find-shard-description mc-state workchain account-int)))
              (%prove (and (= (getf descr :seqno) (tl-get shardblk :seqno))
                           (equalp (getf descr :root-hash) (tl-get shardblk :root-hash))
                           (equalp (getf descr :file-hash) (tl-get shardblk :file-hash))
                           (= (getf descr :shard) (ldb (byte 64 0) (tl-get shardblk :shard))))
                      "the masterchain places the account in shard block ~D (~A), the answer says ~D (~A)"
                      (getf descr :seqno) (octets->hex (getf descr :root-hash))
                      (tl-get shardblk :seqno) (octets->hex (tl-get shardblk :root-hash)))))))
    ;; the shard block, now vouched for, holds the account
    (multiple-value-bind (state block) (%verified-state (parse-boc (tl-get answer :proof)) shardblk "account")
      (declare (ignore block))
      (let ((header (parse-shard-state-header state)))
        (%prove (and (= (getf header :workchain) workchain) (= (getf header :seqno) (tl-get shardblk :seqno))
                     (= (getf header :shard) (ldb (byte 64 0) (tl-get shardblk :shard))))
                "the shard state is of workchain ~D seqno ~D, not the shard block's"
                (getf header :workchain) (getf header :seqno))
        (let* ((accounts (getf header :accounts))
               (state-octets (tl-get answer :state))
               (root (and (= 1 (load-uint (cell-slice accounts) 1)) (load-ref (skip-bits (cell-slice accounts) 1)))))
          (multiple-value-bind (value found) (dict-lookup root account-int 256)
            (if (not found)
                (progn
                  (%prove (zerop (length state-octets)) "the proof shows the account absent but a state was served")
                  (list :exists nil :shard-block shardblk :state-hash (node-hash-at state 0)))
                ;; ShardAccounts leaf: DepthBalanceInfo (split_depth, balance) then ShardAccount
                (let* ((s (skip-bits value 5))                      ; split_depth (#<= 30)
                       (s (nth-value 1 (load-coins s)))             ; balance: grams ...
                       (s (nth-value 1 (load-maybe-ref s))))        ; ... and the extra-currency dictionary
                  (multiple-value-bind (account-ref s) (load-ref s)
                    (multiple-value-bind (trans-hash s) (load-bytes s 32)
                      (let ((trans-lt (load-uint s 64))
                            (served (and (plusp (length state-octets)) (first (parse-boc state-octets)))))
                        (%prove served "the proof shows the account present but no state was served")
                        (%prove (equalp (node-hash-at served 0) (node-hash-at account-ref 0))
                                "the served account state is not the account the proof shows")
                        (list :exists t :account-cell served :last-trans-lt trans-lt
                              :last-trans-hash trans-hash :shard-block shardblk
                              :state-hash (node-hash-at state 0)))))))))))))

;;; --- transactions -----------------------------------------------------------------
;;;
;;; A transaction needs no proof of its own: its cell hash covers everything in it, and each one
;;; names its predecessor by (lt, hash).  So a list is believed when its first element is the
;;; transaction the caller already trusts -- the last_trans_(lt, hash) of a VERIFY-ACCOUNT-STATE
;;; result, or the "previous" pair of a list verified here -- and every next one is the previous
;;; one's named predecessor.  The block ids the liteserver attaches are not proved by anything
;;; (tonlib does not either, for this query): they are returned as hints, never relied on.

(define-proof-function parse-transaction-header (cell)
  "transaction$0111 account_addr:bits256 lt:uint64 prev_trans_hash:bits256 prev_trans_lt:uint64
now:uint32 ...: (:ACCOUNT :LT :PREV-HASH :PREV-LT :NOW :HASH), :HASH being CELL's own hash.  The rest
of the transaction is not read: the hash is what binds it."
  (multiple-value-bind (tag s) (load-uint (cell-slice cell) 4)
    (%prove (= tag 7) "not a transaction cell (tag ~D)" tag)
    (multiple-value-bind (account s) (load-bytes s 32)
      (multiple-value-bind (lt s) (load-uint s 64)
        (multiple-value-bind (prev-hash s) (load-bytes s 32)
          (multiple-value-bind (prev-lt s) (load-uint s 64)
            (list :account account :lt lt :prev-hash prev-hash :prev-lt prev-lt
                  :now (load-uint s 32) :hash (node-hash-at cell 0))))))))

(defun verify-transaction-list (answer account lt hash &key count)
  (with-proof-errors (%verify-transaction-list answer account lt hash count)))

(defun %verify-transaction-list (answer account lt hash count)
  "ANSWER, a decoded liteServer.transactionList (:IDS :TRANSACTIONS), as the answer to a request for
up to COUNT transactions of ACCOUNT (an ADDRESS) starting at the trusted (LT, HASH).  Returns a plist
(:TRANSACTIONS list of (:LT :HASH :PREV-LT :PREV-HASH :NOW :CELL :UNVERIFIED-BLOCK-ID), newest first;
the transactions themselves are proved by the hash chain from the account's proved state, but the block
id served beside each one is only the server's CLAIM -- nothing in this answer proves which block a
transaction is in -- so it is named :UNVERIFIED-BLOCK-ID and must not be relied on)
(:NEXT-LT :NEXT-HASH the predecessor of the last one, to continue with) (:COMPLETE true when that was
the account's first transaction), or signals a PROOF-ERROR.  An empty list for a transaction that
exists, a transaction that is not the expected one, one of another account, a break in the chain
and more than COUNT are all refused."
  (let* ((octets (tl-get answer :transactions))
         (ids (tl-get answer :ids))
         (roots (and (plusp (length octets)) (parse-boc octets)))
         (account-hash (address-hash account))
         (expected-lt lt)
         (expected-hash hash)
         (found '()))
    (%prove (plusp lt) "the start of the list is lt 0: there is no transaction to list")
    (%prove (= 32 (length hash)) "the start hash has ~D bytes" (length hash))
    (%prove roots "no transactions served for the existing transaction (lt ~D)" lt)
    (%prove (= (length roots) (length ids)) "~D transactions but ~D block ids" (length roots) (length ids))
    (%prove (or (null count) (<= (length roots) count)) "~D transactions served, ~D asked for"
            (length roots) count)
    (loop for root in roots
          for id across ids
          for position from 1
          do (let ((h (parse-transaction-header root)))
               (%prove (equalp (getf h :account) account-hash) "a transaction of another account")
               (%prove (= (getf h :lt) expected-lt) "transaction lt ~D where ~D was expected"
                       (getf h :lt) expected-lt)
               (%prove (equalp (getf h :hash) expected-hash) "transaction hash is not the expected one (lt ~D)"
                       expected-lt)
               (%prove (< (getf h :prev-lt) (getf h :lt)) "transaction ~D names a predecessor ~D" (getf h :lt)
                       (getf h :prev-lt))
               (push (list :lt (getf h :lt) :hash (getf h :hash) :prev-lt (getf h :prev-lt)
                           :prev-hash (getf h :prev-hash) :now (getf h :now) :cell root :unverified-block-id id)
                     found)
               (setf expected-lt (getf h :prev-lt)
                     expected-hash (getf h :prev-hash))
               (when (zerop expected-lt)
                 (%prove (= position (length roots)) "transactions served after the account's first"))))
    (list :transactions (nreverse found) :next-lt expected-lt :next-hash expected-hash
          :complete (zerop expected-lt))))

;;; --- block headers, block data, the transactions of a block ------------------------------------

(defun %single-root (octets what)
  (let ((roots (and (plusp (length octets)) (parse-boc octets))))
    (%prove (and roots (null (rest roots))) "~A: ~D roots, one expected" what (length roots))
    (first roots)))

(defun %prove-same-block-id (served expected what)
  "SERVED, the id a liteserver answered with, is EXPECTED: workchain, shard, seqno and both hashes."
  (%prove (and (= (tl-get served :workchain) (tl-get expected :workchain))
               (= (ldb (byte 64 0) (tl-get served :shard)) (ldb (byte 64 0) (tl-get expected :shard)))
               (= (tl-get served :seqno) (tl-get expected :seqno))
               (equalp (tl-get served :root-hash) (tl-get expected :root-hash))
               (equalp (tl-get served :file-hash) (tl-get expected :file-hash)))
          "~A: the answer is for another block than the one asked for" what))

(defun verify-block-header (answer block-id)
  (with-proof-errors
    (%prove-same-block-id (tl-get answer :id) block-id "block header")
    (multiple-value-bind (block state-hash info)
        (verify-block-proof (%single-root (tl-get answer :header-proof) "block header") block-id)
      (declare (ignore block))
      (list :info info :state-hash state-hash))))

(setf (documentation 'verify-block-header 'function)
      "ANSWER, a decoded liteServer.blockHeader, for BLOCK-ID (a blockIdExt the caller trusts, or has
yet to place in the chain: a header proves a block's contents, not that the block is canonical).
Returns (:INFO the parsed BlockInfo :STATE-HASH the hash of the state after the block) or signals a
PROOF-ERROR: the id must be the one asked for and the header proof must be a Merkle proof of that
block hash whose BlockInfo agrees with the id.  For liteServer.lookupBlock by lt or utime the caller
reads :START-LT, :END-LT and :GEN-UTIME of :INFO itself: only the seqno of a seqno lookup is checked
by the id.")

(defun verify-block-data (answer block-id)
  (with-proof-errors
    (%prove-same-block-id (tl-get answer :id) block-id "block data")
    (let* ((octets (tl-get answer :data))
           (root (%single-root octets "block data")))
      (%prove (equalp (sha256 octets) (tl-get block-id :file-hash)) "block data: the file hash is not the id's")
      (%prove (equalp (node-hash-at root 0) (tl-get block-id :root-hash)) "block data: the root hash is not the id's")
      (%prove (and (cell-p root) (not (cell-exotic-p root))) "block data: the root is not an ordinary cell")
      (%prove (= (load-uint (cell-slice root) 32) #x11ef55aa) "block data: not a Block cell")
      (%prove (= 4 (length (cell-refs root))) "block data: a Block has four references")
      (let ((info (parse-block-info (svref (cell-refs root) 0))))
        (%prove (and (= (getf info :seqno) (tl-get block-id :seqno))
                     (= (getf info :workchain) (tl-get block-id :workchain))
                     (= (getf info :shard) (ldb (byte 64 0) (tl-get block-id :shard))))
                "block data: BlockInfo disagrees with the id")
        (list :block root :info info)))))

(setf (documentation 'verify-block-data 'function)
      "ANSWER, a decoded liteServer.blockData, for BLOCK-ID (a blockIdExt the caller trusts): the data
must hash (SHA-256 of the served octets) to the id's file hash, its single root to the id's root hash,
be a Block, and its BlockInfo must agree with the id.  Returns (:BLOCK root cell :INFO BlockInfo).")

(defun %skip-currency-collection (s)
  "The rest of S after a CurrencyCollection (grams and an optional extra-currencies dictionary)."
  (let ((s (nth-value 1 (load-coins s))))
    (multiple-value-bind (present s) (load-uint s 1)
      (if (= present 1) (nth-value 1 (load-ref s)) s))))

(define-proof-function find-block-transaction (block account lt)
  "BLOCK, a Block cell with its account blocks revealed.  The transaction cell of ACCOUNT (32 octets)
at logical time LT in it (VALUES CELL FOUND-P); FOUND-P is false when the proof shows there is none.
The path is account_blocks -> AccountBlock -> transactions (a HashmapAug 64 stored inline in the
AccountBlock) as block::get_block_transaction reads it."
  (%prove (= 4 (length (cell-refs block))) "a Block has four references")
  (let ((extra (svref (cell-refs block) 3)))
    (%prove (= (load-uint (cell-slice extra) 32) #x4a33f6fd) "not a BlockExtra cell")
    (%prove (<= 3 (length (cell-refs extra))) "a BlockExtra has at least three references")
    (multiple-value-bind (present s) (load-uint (cell-slice (svref (cell-refs extra) 2)) 1)
      (if (zerop present)
          (values nil nil)
          (multiple-value-bind (value found) (dict-lookup (load-ref s) (octets->uint account) 256)
            (if (not found)
                (values nil nil)
                (multiple-value-bind (tag s) (load-uint (%skip-currency-collection value) 4)
                  (%prove (= tag 5) "not an AccountBlock (tag ~D)" tag)
                  (multiple-value-bind (addr s) (load-bytes s 32)
                    (%prove (equalp addr account) "an AccountBlock of another account than its key")
                    (multiple-value-bind (leaf found) (dict-lookup-in-slice s lt 64)
                      (if (not found)
                          (values nil nil)
                          (values (load-ref (%skip-currency-collection leaf)) t)))))))))))

(defun verify-block-transactions (answer block-id &key count reverse)
  (with-proof-errors
    (%prove-same-block-id (tl-get answer :id) block-id "block transactions")
    (let* ((ids (coerce (tl-get answer :ids) 'list))
           (octets (tl-get answer :proof))
           (previous nil))
      (%prove (or (null count) (<= (length ids) count)) "~D transactions served, ~D asked for"
              (length ids) count)
      (if (null ids)
          (list :transactions '() :incomplete (and (tl-get answer :incomplete) t))
      (let ((block (verify-merkle-proof (%single-root octets "block transactions proof")
                                        (tl-get block-id :root-hash))))
        (%prove (and (cell-p block) (not (cell-exotic-p block))
                     (= (load-uint (cell-slice block) 32) #x11ef55aa))
                "block transactions: the proof is not of a Block")
        (list :transactions
              (loop for id in ids
                    collect (let ((account (tl-get id :account)) (lt (tl-get id :lt)) (hash (tl-get id :hash)))
                              (%prove (and (= 7 (logand 7 (tl-get id :mode))) account lt hash)
                                      "block transactions: an id without account, lt and hash")
                              (let ((key (cons (octets->uint account) lt)))
                                (%prove (or (null previous)
                                            (if reverse
                                                (or (> (car previous) (car key))
                                                    (and (= (car previous) (car key)) (> (cdr previous) (cdr key))))
                                                (or (< (car previous) (car key))
                                                    (and (= (car previous) (car key)) (< (cdr previous) (cdr key))))))
                                        "block transactions are not in strict ~:[ascending~;descending~] order"
                                        reverse)
                                (setf previous key))
                              (multiple-value-bind (tx found) (find-block-transaction block account lt)
                                (%prove found "the block has no transaction of this account at lt ~D" lt)
                                (%prove (equalp (node-hash-at tx 0) hash)
                                        "the block's transaction at lt ~D is not the one listed" lt))
                              (list :account account :lt lt :hash hash)))
              :incomplete (and (tl-get answer :incomplete) t)))))))

(setf (documentation 'verify-block-transactions 'function)
      "ANSWER, a decoded liteServer.blockTransactions, for BLOCK-ID (a blockIdExt the caller trusts), as
the answer to a request for up to COUNT transactions (REVERSE when asked in reverse order).  Every
listed (account, lt, hash) must be proved, by a Merkle proof of the block, to be a transaction of
that block; the list must be in strict (account, lt) order.  Returns (:TRANSACTIONS list of
(:ACCOUNT :LT :HASH) :INCOMPLETE the flag as served).  Proves what is listed, NOT that nothing is
left out: completeness is not provable from the proof.")

;;; --- accounts ---------------------------------------------------------------------------------

(define-proof-function parse-account (cell)
  "The fields of an Account cell (as VERIFY-ACCOUNT-STATE returns it; NIL or account_none: nothing):
(:STATUS :NONEXISTENT | :UNINIT | :FROZEN | :ACTIVE, and for an existing account :ADDRESS :BALANCE
(nanotons) :LAST-TRANS-LT; :FROZEN-HASH for a frozen one; :CODE :DATA :LIBRARY-ROOT (cells or NIL) for an
active one).  account$1 addr:MsgAddressInt storage_stat:StorageInfo storage:AccountStorage.

StorageInfo has had two layouts: used:(cells bits public_cells) last_paid due_payment, and the newer
used:(cells bits) storage_extra:StorageExtraInfo last_paid due_payment, where storage_extra is
storage_extra_none$000 (the very bits of a zero public_cells, so both layouts read alike) or
storage_extra_info$001 dict_hash:uint256 (an account with a large storage: the old layout reads it wrongly,
and then the account looks frozen or empty).  Both are tried and the one that consumes the whole cell wins;
the old one is the fallback for a cell neither fits."
  (if (or (null cell) (zerop (load-uint (cell-slice cell) 1)))
      (list :status :nonexistent)
      (multiple-value-bind (address s0) (load-address (nth-value 1 (load-uint (cell-slice cell) 1)))
        (labels ((skip-var7 (s) (multiple-value-bind (n s) (load-uint s 3) (skip-bits s (* 8 n))))
                 (try (layout)
                   ;; (VALUES PLIST FINAL-SLICE) for LAYOUT (:OLD or :NEW)
                   (let* ((s (skip-var7 (skip-var7 s0)))
                          (s (ecase layout
                               (:old (skip-var7 s))
                               (:new (multiple-value-bind (tag s) (load-uint s 3)
                                       (case tag
                                         (0 s)
                                         (1 (skip-bits s 256))
                                         (t (ton-error "storage_extra: unknown tag ~D" tag)))))))
                          (s (skip-bits s 32)))
                     (multiple-value-bind (due s) (load-bit s)
                       (when due (setf s (nth-value 1 (load-coins s))))
                       (multiple-value-bind (last-trans-lt s) (load-uint s 64)
                         (multiple-value-bind (balance s) (load-coins s)
                           (let ((s (nth-value 1 (load-maybe-ref s)))     ; the extra currencies
                                 (base (list :address address :balance balance :last-trans-lt last-trans-lt)))
                             (multiple-value-bind (active s) (load-bit s)
                               (if active
                                   ;; StateInit: split_depth, special, code, data, library
                                   (let ((s s))
                                     (multiple-value-bind (has s2) (load-bit s) (setf s (if has (skip-bits s2 5) s2)))
                                     (multiple-value-bind (has s2) (load-bit s) (setf s (if has (skip-bits s2 2) s2)))
                                     (multiple-value-bind (code s2) (load-maybe-ref s)
                                       (multiple-value-bind (data s3) (load-maybe-ref s2)
                                         (multiple-value-bind (has s4) (load-bit s3)
                                           (values (list* :status :active :code code :data data
                                                          :library-root (and has (load-ref s4)) base)
                                                   (if has (nth-value 1 (load-ref s4)) s4))))))
                                   (multiple-value-bind (frozen s) (load-bit s)
                                     (if frozen
                                         (multiple-value-bind (h s) (load-bytes s 32)
                                           (values (list* :status :frozen :frozen-hash h base) s))
                                         (values (list* :status :uninit base) s))))))))))))
          (let ((candidates '()))
            (dolist (layout '(:old :new))
              (handler-case
                  (multiple-value-bind (plist final) (try layout)
                    (push (cons plist (slice-empty-p final)) candidates))
                (error () nil)))
            (setf candidates (nreverse candidates))
            (let ((exact (find-if #'cdr candidates)))
              (cond (exact (car exact))
                    (candidates (car (first candidates)))
                    (t (error 'proof-error :format-control "an account cell that no StorageInfo layout reads"
                                           :format-arguments '())))))))))

;;; --- libraries and sent messages -----------------------------------------------------------------

(defun verify-libraries (answer requested)
  (with-proof-errors
    (let ((seen '()))
      (loop for entry across (coerce (tl-get answer :result) 'vector)
            collect (let ((hash (tl-get entry :hash)))
                      (%prove (find hash requested :test #'equalp) "a library that was not asked for")
                      (%prove (not (member hash seen :test #'equalp)) "a library served twice")
                      (push hash seen)
                      (let ((root (%single-root (tl-get entry :data) "library")))
                        (%prove (equalp (node-hash-at root 0) hash) "a library whose cell hashes to another value")
                        (cons hash root)))))))

(defun %skip-cc-flagged (s)
  "(VALUES REST HAS-EXTRA-REF) past a CurrencyCollection: grams (VarUInteger 16), then the extra-currency
dictionary's presence bit."
  (multiple-value-bind (len s) (load-uint s 4)
    (multiple-value-bind (bit s) (load-uint (skip-bits s (* 8 len)) 1)
      (values s (= bit 1)))))

(define-proof-function %state-libraries-root (state)
  "The root cell of the libraries dictionary (HashmapE 256 LibDescr) of the ShardStateUnsplit STATE,
NIL when it is empty.  It lives in the ^[overload_history underload_history total_balance
total_validator_fees libraries master_ref] cell, after the extra-currency references."
  (%prove (>= (length (cell-refs state)) 3) "state: too few references")
  (let* ((tail (svref (cell-refs state) 2))
         (s (skip-bits (cell-slice tail) 128)))
    (multiple-value-bind (s extra1) (%skip-cc-flagged s)
      (multiple-value-bind (s extra2) (%skip-cc-flagged s)
        (and (= 1 (load-uint s 1))
             (let ((index (+ (if extra1 1 0) (if extra2 1 0))))
               (%prove (< index (length (cell-refs tail))) "state: the libraries dictionary reference is missing")
               (svref (cell-refs tail) index)))))))

(setf (documentation 'verify-libraries 'function)
      "ANSWER, a decoded liteServer.libraryResult, to a request for the libraries of REQUESTED (a list of
32-octet hashes).  A library is identified by the hash of its cell, so every served entry must be a
single-root BOC whose root hashes to the entry's hash, asked for and served once; libraries the
chain does not have may be left out.  Returns a list of (HASH . CELL).  The plain query carries no
proof that a library is PUBLISHED on the masterchain, which does not matter for what the cell
contains.  (liteServer.getLibrariesWithProof is not verified here: its proof layout needs the node's
source.)")

(defun check-send-message-status (answer)
  "The status of a liteServer.sendMsgStatus: 1 means the liteserver took the message, anything else is a
TON-ERROR (the message is NOT sent).  Returns the status."
  (let ((status (tl-get answer :status)))
    (unless (eql status 1)
      (ton-error "the liteserver did not accept the message (status ~D)" status))
    status))

(defun external-message-hash (octets)
  "The hash of the message in the BOC OCTETS, which is what raw.sendMessageReturnHash reports: the
hash of the single root cell."
  (node-hash-at (%single-root octets "message") 0))

;;; --- the shards of a masterchain block ------------------------------------------------------------

(define-proof-function list-shard-descriptions (dict-root)
  "The shards in the ShardHashes dictionary rooted at DICT-ROOT (a HashmapE 32 ^(BinTree ShardDescr),
NIL when empty), as a list of plists (:WORKCHAIN :SHARD :SEQNO :REG-MC-SEQNO :START-LT :END-LT :ROOT-HASH
:FILE-HASH), the shard being its 64-bit id.  Every cell must be readable."
  (let ((out '()))
    (labels ((leaf (s workchain depth prefix)
               (multiple-value-bind (tag s) (load-uint s 4)
                 (%prove (member tag '(#xa #xb)) "unexpected ShardDescr constructor ~D" tag)
                 (multiple-value-bind (seqno s) (load-uint s 32)
                   (multiple-value-bind (reg-mc s) (load-uint s 32)
                     (multiple-value-bind (start-lt s) (load-uint s 64)
                       (multiple-value-bind (end-lt s) (load-uint s 64)
                         (multiple-value-bind (root-hash s) (load-bytes s 32)
                           (push (list :workchain workchain
                                       :shard (logior (ash prefix (- 64 depth)) (ash 1 (- 63 depth)))
                                       :seqno seqno :reg-mc-seqno reg-mc :start-lt start-lt :end-lt end-lt
                                       :root-hash root-hash :file-hash (load-bytes s 32))
                                 out))))))))
             (walk (cell workchain depth prefix)
               (%prove (<= depth 60) "shard tree deeper than 60 levels")
               (let ((s (cell-slice cell)))
                 (if (zerop (load-uint s 1))
                     (leaf (skip-bits s 1) workchain depth prefix)
                     (multiple-value-bind (left s2) (load-ref (skip-bits s 1))
                       (walk left workchain (1+ depth) (ash prefix 1))
                       (walk (load-ref s2) workchain (1+ depth) (1+ (ash prefix 1))))))))
      (dolist (entry (dict-entries dict-root 32 (lambda (s) (load-ref s))))
        (let ((key (car entry)))
          (walk (cdr entry) (if (>= key #x80000000) (- key #x100000000) key) 0 0))))
    (nreverse out)))

(defun verify-all-shards-info (answer mc-block-id)
  (with-proof-errors
    (%prove-same-block-id (tl-get answer :id) mc-block-id "all shards info")
    (let* ((block (verify-merkle-proof (%single-root (tl-get answer :proof) "all shards info proof")
                                       (tl-get mc-block-id :root-hash)))
           (data (%single-root (tl-get answer :data) "all shards info data")))
      (%prove (and (not (cell-exotic-p block)) (= (load-uint (cell-slice block) 32) #x11ef55aa)
                   (= 4 (length (cell-refs block))))
              "all shards info: the proof is not of a Block")
      (let* ((extra (svref (cell-refs block) 3))
             (extra-slice (cell-slice extra)))
        (%prove (= (load-uint extra-slice 32) #x4a33f6fd) "all shards info: not a BlockExtra")
        (%prove (= 1 (load-uint (skip-bits extra-slice 544) 1)) "the masterchain block has no McBlockExtra")
        (%prove (= 4 (length (cell-refs extra))) "all shards info: a BlockExtra with a custom part has four references")
        (let* ((custom (svref (cell-refs extra) 3))
               (s (cell-slice custom)))
          (%prove (= (load-uint s 16) #xcca5) "all shards info: not a McBlockExtra")
          (multiple-value-bind (present s) (load-uint (skip-bits s 17) 1)
            (let ((data-slice (cell-slice data)))
              (multiple-value-bind (data-present data-slice) (load-uint data-slice 1)
                (%prove (= present data-present) "the served ShardHashes and the block's disagree on being empty")
                (if (zerop present)
                    (progn (%prove (and (zerop (slice-remaining-bits data-slice)) (zerop (length (cell-refs data))))
                                   "all shards info: junk after an empty ShardHashes")
                           (list :shards '()))
                    (let ((proved (load-ref s))
                          (served (load-ref data-slice)))
                      (%prove (and (zerop (slice-remaining-bits data-slice)) (= 1 (length (cell-refs data))))
                              "all shards info: junk after the ShardHashes root")
                      (%prove (equalp (node-hash-at proved 0) (node-hash-at served 0))
                              "the served ShardHashes are not the ones the block commits to")
                      (list :shards (list-shard-descriptions served))))))))))))

(setf (documentation 'verify-all-shards-info 'function)
      "ANSWER, a decoded liteServer.allShardsInfo, for MC-BLOCK-ID (a masterchain blockIdExt the caller
trusts).  The proof must be a Merkle proof of that block revealing its McBlockExtra; the served
ShardHashes dictionary must hash (root) to the one the McBlockExtra names.  Returns (:SHARDS list of
plists, see LIST-SHARD-DESCRIPTIONS): the shard blocks the masterchain block refers to, which are as
trustworthy as MC-BLOCK-ID.")

;;; --- getShardInfo ------------------------------------------------------------------------
;;;
;;; liteserver.cpp continue_getShardInfo: shard_proof is a BOC of TWO Merkle proofs (the masterchain
;;; block -> its state hash, then the masterchain STATE revealing McStateExtra and the lookup path in
;;; shard_hashes); shard_descr is the BinTree leaf the lookup ended at (ShardDescr behind a 0 bit),
;;; shardblk the block it names -- or, when nothing was found, the cleared invalid id (workchain
;;; 0x80000000, shard 0, seqno 0, zero hashes) and an empty shard_descr.  The lookup is
;;; ShardConfig::get_shard_hash_raw_from, redone here over the PROVED tree.

(defconstant +invalid-workchain+ (- (expt 2 31)))

(defun %shard-pfx-len (shard)
  (if (zerop shard) 0 (- 63 (1- (integer-length (logand shard (- shard)))))))

(define-proof-function %mc-state-shard-hashes (mc-state)
  "The ShardHashes dictionary root (a cell, or NIL when empty) of the masterchain state MC-STATE."
  (let ((custom (getf (parse-shard-state-header mc-state) :custom)))
    (%prove custom "masterchain state has no McStateExtra")
    (let ((s (cell-slice custom)))
      (%prove (= (load-uint s 16) #xcc26) "masterchain state: not a McStateExtra")
      (load-maybe-ref (skip-bits s 16)))))

(define-proof-function lookup-shard-leaf (dict-root workchain shard exact)
  "ShardConfig::get_shard_hash_raw_from over DICT-ROOT (ShardHashes): (VALUES LEAF-CELL TRUE-SHARD) for
the BinTree leaf that covers SHARD of WORKCHAIN (with EXACT only a leaf of that very shard), NIL when
there is none: the masterchain, an invalid shard, a workchain without shards, or SHARD an ancestor of
several leaves.  Every cell on the way must be readable."
  (when (or (= workchain -1) (= workchain +invalid-workchain+) (zerop (ldb (byte 64 0) shard)))
    (return-from lookup-shard-leaf nil))
  (multiple-value-bind (value found) (dict-lookup dict-root (ldb (byte 32 0) workchain) 32)
    (unless found (return-from lookup-shard-leaf nil))
    (let* ((mask (1- (expt 2 64)))
           (id (ldb (byte 64 0) shard))
           (len (%shard-pfx-len id))
           (z id)
           (depth 0)
           (cell (load-ref value)))
      (loop
        (let ((s (cell-slice cell)))
          (if (zerop (load-uint s 1))
              (return
                (if (and (plusp len) exact)
                    nil
                    (let ((m (ash mask (- depth))))
                      (values cell (ldb (byte 64 0) (- (logior id m) (ash m -1)))))))
              (progn
                (when (zerop len) (return nil))
                (%prove (and (= 2 (length (cell-refs cell))) (zerop (slice-remaining-bits (skip-bits s 1))))
                        "a shard tree fork is not two references")
                (setf cell (svref (cell-refs cell) (ldb (byte 1 63) z))
                      z (ldb (byte 64 0) (ash z 1)))
                (decf len)
                (incf depth))))))))

(define-proof-function %read-shard-descr (leaf)
  "(:SEQNO :ROOT-HASH :FILE-HASH) of a BinTree leaf cell: a 0 bit, then a ShardDescr."
  (let ((s (cell-slice leaf)))
    (%prove (zerop (load-uint s 1)) "a shard tree node that is not a leaf")
    (multiple-value-bind (tag s) (load-uint (skip-bits s 1) 4)
      (%prove (member tag '(#xa #xb)) "unexpected ShardDescr constructor ~D" tag)
      (multiple-value-bind (seqno s) (load-uint s 32)
        (multiple-value-bind (root-hash s) (%fetch-hash (skip-bits s 160)) ; reg_mc_seqno, start_lt, end_lt
          (list :seqno seqno :root-hash root-hash :file-hash (%fetch-hash s)))))))

(defun verify-shard-info (answer mc-block-id workchain shard &key exact)
  (with-proof-errors
    (%prove-same-block-id (tl-get answer :id) mc-block-id "shard info")
    (let* ((roots (and (plusp (length (tl-get answer :shard-proof))) (parse-boc (tl-get answer :shard-proof))))
           (mc-state (%verified-state roots mc-block-id "shard info"))
           (served (tl-get answer :shard-descr))
           (shardblk (tl-get answer :shardblk)))
      (multiple-value-bind (leaf true-shard)
          (lookup-shard-leaf (%mc-state-shard-hashes mc-state) workchain shard exact)
        (if (null leaf)
            (progn
              (%prove (and (= (tl-get shardblk :workchain) +invalid-workchain+)
                           (zerop (tl-get shardblk :shard)) (zerop (tl-get shardblk :seqno))
                           (= 32 (length (tl-get shardblk :root-hash))) (every #'zerop (tl-get shardblk :root-hash))
                           (= 32 (length (tl-get shardblk :file-hash))) (every #'zerop (tl-get shardblk :file-hash))
                           (zerop (length served)))
                      "the proof shows no such shard, but the answer names one")
              (list :found nil :shard-block nil))
            (let ((descr (%read-shard-descr leaf)))
              (%prove (and (= (tl-get shardblk :workchain) workchain)
                           (= (ldb (byte 64 0) (tl-get shardblk :shard)) true-shard)
                           (= (tl-get shardblk :seqno) (getf descr :seqno))
                           (equalp (tl-get shardblk :root-hash) (getf descr :root-hash))
                           (equalp (tl-get shardblk :file-hash) (getf descr :file-hash)))
                      "the proof names another shard block than the answer's")
              (%prove (equalp (node-hash-at (%single-root served "shard description") 0)
                              (node-hash-at leaf 0))
                      "the served shard description is not the leaf the proof shows")
              (list :found t :shard-block shardblk :shard true-shard :seqno (getf descr :seqno)
                    :root-hash (getf descr :root-hash) :file-hash (getf descr :file-hash))))))))

;;; --- lookupBlockWithProof ------------------------------------------------------------------
;;;
;;; The reference is tonlib's check_lookup_block_proof (TonlibClient.cpp) with block::
;;; unpack_block_prev_blk_ext (block.cpp) and check_old_mc_block_id.  The answer places one block
;;; (workchain, shard, seqno | lt | utime) in the chain the client trusts: the masterchain block ALT
;;; that includes it is either the trusted block or one of its prev_blocks; from ALT a chain of
;;; Merkle-proved blocks leads down to the answered block (the masterchain block names the shard's top
;;; block, each shard block names its predecessors); the block's own header proof binds the id; for lt
;;; and utime the PREVIOUS block's header shows that no earlier block qualifies.

(defun %signed64 (x) (let ((x (ldb (byte 64 0) x))) (if (>= x (expt 2 63)) (- x (expt 2 64)) x)))

(defun %shard-lowbit (x) (logand x (- x)))

(defun %shard-id-contains-p (parent child)
  "shard_contains(parent, child) over 64-bit shard ids: CHILD is PARENT or inside it."
  (let ((parent (ldb (byte 64 0) parent)) (child (ldb (byte 64 0) child)))
    (and (plusp parent) (plusp child)
         (zerop (logand (logxor parent child)
                        (ldb (byte 64 0) (ash (ldb (byte 64 0) (- (%shard-lowbit parent))) 1)))))))

(defun %shard-parent (x)
  (let ((low (%shard-lowbit x))) (ldb (byte 64 0) (logior (- x low) (ash low 1)))))

(defun %shard-child (x leftp)
  (let ((half (ash (%shard-lowbit x) -1))) (if leftp (- x half) (+ x half))))

(define-proof-function %read-ext-blk-ref (cell)
  "(:END-LT :SEQNO :ROOT-HASH :FILE-HASH) of an ExtBlkRef cell."
  (let ((s (cell-slice cell)))
    (multiple-value-bind (end-lt s) (load-uint s 64)
      (multiple-value-bind (seqno s) (load-uint s 32)
        (multiple-value-bind (root s) (load-bytes s 32)
          (list :end-lt end-lt :seqno seqno :root-hash root :file-hash (load-bytes s 32)))))))

(define-proof-function parse-block-links (block id)
  "unpack_block_prev_blk_ext over the Block cell BLOCK, which must be block ID (a blockIdExt tl-obj:
workchain, shard, seqno and root hash): (VALUES PREV MC-REF AFTER-SPLIT), PREV a list of plists
(:WORKCHAIN :SHARD :SEQNO :ROOT-HASH :FILE-HASH) -- one predecessor, or two after a merge -- and MC-REF
the masterchain block a shard block was built on (NIL for a masterchain block)."
  (%prove (and (cell-p block) (not (cell-exotic-p block)) (= 4 (length (cell-refs block)))
               (= (load-uint (cell-slice block) 32) #x11ef55aa))
          "block header: not a Block cell")
  (%prove (equalp (node-hash-at block 0) (tl-get id :root-hash)) "block header: another block than expected")
  (let* ((info-cell (svref (cell-refs block) 0))
         (info (parse-block-info info-cell))
         (s (skip-bits (cell-slice info-cell) 64)))
    (multiple-value-bind (not-master s) (load-uint s 1)
      (multiple-value-bind (after-merge s) (load-uint s 1)
        (multiple-value-bind (before-split s) (load-uint s 1)
          (declare (ignore before-split))
          (let* ((after-split (load-uint s 1))
                 (workchain (getf info :workchain)) (shard (getf info :shard)) (seqno (getf info :seqno))
                 (refs (cell-refs info-cell))
                 (mc-index (if (= not-master 1) 0 nil))
                 (prev-cell (svref refs (if mc-index 1 0))))
            (%prove (and (= workchain (tl-get id :workchain)) (= shard (ldb (byte 64 0) (tl-get id :shard)))
                         (= seqno (tl-get id :seqno)))
                    "block header contains another block id than expected")
            (%prove (eq (= not-master 1) (/= workchain -1)) "block has an invalid not_master flag")
            (let ((prev '()) (prev-seqno 0))
              (cond ((= after-merge 1)
                     (%prove (zerop after-split) "a shard cannot be split and merged at one block")
                     (%prove (and (= 2 (length (cell-refs prev-cell))) (zerop (slice-remaining-bits (cell-slice prev-cell))))
                             "invalid previous block references in block header")
                     (let ((p1 (%read-ext-blk-ref (svref (cell-refs prev-cell) 0)))
                           (p2 (%read-ext-blk-ref (svref (cell-refs prev-cell) 1))))
                       (%prove (and (plusp (getf p1 :seqno)) (plusp (getf p2 :seqno)))
                               "shardchains cannot be merged immediately after initial state")
                       (setf prev (list (list* :workchain workchain :shard (%shard-child shard t) p1)
                                        (list* :workchain workchain :shard (%shard-child shard nil) p2))
                             prev-seqno (max (getf p1 :seqno) (getf p2 :seqno)))))
                    (t
                     (let ((p1 (%read-ext-blk-ref prev-cell)))
                       (%prove (not (and (= after-split 1) (zerop (getf p1 :seqno))))
                               "shardchains cannot be split immediately after initial state")
                       (setf prev (list (list* :workchain workchain
                                               :shard (if (= after-split 1) (%shard-parent shard) shard) p1))
                             prev-seqno (getf p1 :seqno)))))
              (%prove (= seqno (1+ prev-seqno)) "a block's seqno is not one more than its ancestors'")
              (values (mapcar (lambda (p) (list :workchain (getf p :workchain) :shard (getf p :shard)
                                                :seqno (getf p :seqno) :root-hash (getf p :root-hash)
                                                :file-hash (getf p :file-hash)))
                              prev)
                      (and mc-index (%read-ext-blk-ref (svref refs 0)))
                      (= after-split 1)))))))))

(define-proof-function %mc-block-shard-hashes (block)
  "The ShardHashes dictionary root (a cell or NIL) of a masterchain Block cell, read through
BlockExtra and McBlockExtra."
  (%prove (and (not (cell-exotic-p block)) (= (load-uint (cell-slice block) 32) #x11ef55aa)
               (= 4 (length (cell-refs block))))
          "the proof is not of a Block")
  (let* ((extra (svref (cell-refs block) 3))
         (es (cell-slice extra)))
    (%prove (= (load-uint es 32) #x4a33f6fd) "not a BlockExtra")
    (%prove (= 1 (load-uint (skip-bits es 544) 1)) "the masterchain block has no McBlockExtra")
    (%prove (= 4 (length (cell-refs extra))) "a BlockExtra with a custom part has four references")
    (let* ((custom (svref (cell-refs extra) 3))
           (s (cell-slice custom)))
      (%prove (= (load-uint s 16) #xcca5) "not a McBlockExtra")
      (and (= 1 (load-uint (skip-bits s 17) 1)) (load-ref (skip-bits s 18))))))

(define-proof-function %prev-blocks-contain-p (state seqno root-hash file-hash)
  "check_old_mc_block_id: the masterchain STATE's prev_blocks lists the masterchain block (SEQNO, ROOT-HASH,
FILE-HASH)."
  (let* ((custom (getf (parse-shard-state-header state) :custom)))
    (%prove custom "masterchain state has no McStateExtra")
    (let ((s (cell-slice custom)))
      (%prove (= (load-uint s 16) #xcc26) "masterchain state: not a McStateExtra")
      (let* ((present (load-uint (skip-bits s 16) 1))
             (r1 (svref (cell-refs custom) (if (= present 1) 2 1)))
             (rs (skip-bits (cell-slice r1) 81)))       ; flags (16), validator_info (65)
        (and (= 1 (load-uint rs 1))
             (multiple-value-bind (value found) (dict-lookup (load-ref (skip-bits rs 1)) seqno 32)
               (and found
                    (let ((ref (%read-ext-blk-ref-slice (skip-bits value 66)))) ; extra (65), key
                      (and (= (getf ref :seqno) seqno)
                           (equalp (getf ref :root-hash) root-hash)
                           (equalp (getf ref :file-hash) file-hash))))))))))

(define-proof-function %read-ext-blk-ref-slice (s)
  (multiple-value-bind (end-lt s) (load-uint s 64)
    (multiple-value-bind (seqno s) (load-uint s 32)
      (multiple-value-bind (root s) (load-bytes s 32)
        (list :end-lt end-lt :seqno seqno :root-hash root :file-hash (load-bytes s 32))))))

(defun %verify-shard-link-chain (start links)
  "START, a block id the caller has placed in the trusted chain, followed along LINKS (a vector of
liteServer.shardBlockLink, as in a lookupBlockWithProof or a getShardBlockProof answer): from a
masterchain block to the top block of a shard through its ShardHashes, from a shard block to one of
its previous blocks through its BlockInfo.  Returns the id the chain ends at.  Run under WITH-PROOF-ERRORS."
  (let ((cur start))
    (dolist (link (coerce links 'list) cur)
        (let* ((next (tl-get link :id))
               (root (handler-case
                         (verify-merkle-proof (%single-root (tl-get link :proof) "shard link proof")
                                              (tl-get cur :root-hash))
                       (boc-error (e) (%prove nil "invalid block hash in a proof link: ~A" e)))))
          (if (= (tl-get cur :workchain) -1)
              (multiple-value-bind (leaf true-shard)
                  (lookup-shard-leaf (%mc-block-shard-hashes root) (tl-get next :workchain) (tl-get next :shard) t)
                (%prove leaf "invalid proof chain: the shard is not in the masterchain block's shard list")
                (let ((descr (%read-shard-descr leaf)))
                  (%prove (and (= true-shard (ldb (byte 64 0) (tl-get next :shard)))
                               (= (getf descr :seqno) (tl-get next :seqno))
                               (equalp (getf descr :root-hash) (tl-get next :root-hash))
                               (equalp (getf descr :file-hash) (tl-get next :file-hash)))
                          "invalid proof chain: the block is not the masterchain's top block of its shard")))
              (let ((prev (parse-block-links root cur)))
                (%prove (some (lambda (p) (and (= (getf p :workchain) (tl-get next :workchain))
                                               (= (getf p :shard) (ldb (byte 64 0) (tl-get next :shard)))
                                               (= (getf p :seqno) (tl-get next :seqno))
                                               (equalp (getf p :root-hash) (tl-get next :root-hash))
                                               (equalp (getf p :file-hash) (tl-get next :file-hash))))
                              prev)
                        "invalid proof chain: the block is not among the previous blocks")))
          (setf cur next)))))

(defun verify-lookup-block (answer trusted-mc-block workchain shard mode &key (seqno 0) (lt 0) (utime 0))
  (with-proof-errors
    (%prove (member (logand mode 7) '(1 2 4)) "lookup mode ~D: exactly one of the seqno, lt, utime bits" mode)
    (let* ((alt (tl-get answer :mc-block-id))
           (answered (tl-get answer :id))
           (cur alt))
      (%prove (and (= (tl-get alt :workchain) -1) (= (ldb (byte 64 0) (tl-get alt :shard)) (expt 2 63)))
              "invalid response: the masterchain block id is not of the masterchain")
      ;; 1. ALT is the trusted block, or one of its prev_blocks
      (unless (and (= (tl-get alt :seqno) (tl-get trusted-mc-block :seqno))
                   (equalp (tl-get alt :root-hash) (tl-get trusted-mc-block :root-hash))
                   (equalp (tl-get alt :file-hash) (tl-get trusted-mc-block :file-hash)))
        (multiple-value-bind (block state-hash)
            (verify-block-proof (%single-root (tl-get answer :client-mc-state-proof) "client masterchain state proof")
                                trusted-mc-block)
          (declare (ignore block))
          (let ((state (handler-case
                           (verify-merkle-proof (%single-root (tl-get answer :mc-block-proof) "masterchain state proof")
                                                state-hash)
                         (boc-error (e) (%prove nil "masterchain state proof: ~A" e)))))
            (%prove (%prev-blocks-contain-p state (tl-get alt :seqno) (tl-get alt :root-hash) (tl-get alt :file-hash))
                    "the trusted masterchain state does not list the block ~D the answer starts from"
                    (tl-get alt :seqno)))))
      ;; 2. the chain from ALT down to the answered block
      (setf cur (%verify-shard-link-chain cur (tl-get answer :shard-links)))
      (%prove (and (= (tl-get cur :workchain) workchain) (%shard-id-contains-p (tl-get cur :shard) shard))
              "the response block has another workchain or shard than asked for")
      (%prove-same-block-id answered cur "lookup")
      ;; 3. the header of the answered block
      (let* ((header (handler-case
                         (verify-merkle-proof (%single-root (tl-get answer :header) "lookup header") (tl-get cur :root-hash))
                       (boc-error (e) (%prove nil "invalid header hash in proof: ~A" e)))))
        (multiple-value-bind (prev) (parse-block-links header cur)
          (let ((info (parse-block-info (svref (cell-refs header) 0))))
            (cond
              ((logtest mode 1)
               (%prove (= (tl-get cur :seqno) seqno) "invalid seqno in proof"))
              (t
               (let* ((prev-root-cell (%single-root (tl-get answer :prev-header) "lookup prev header"))
                      (prev-hash (node-hash-at (merkle-proof-root prev-root-cell) 0))
                      (p (find-if (lambda (p) (equalp (getf p :root-hash) prev-hash)) prev)))
                 (%prove p "invalid prev header hash in proof")
                 (%prove (%shard-id-contains-p (getf p :shard) shard) "invalid prev header shard in proof")
                 (let* ((prev-block (verify-merkle-proof prev-root-cell prev-hash))
                        (prev-info (parse-block-info (svref (cell-refs prev-block) 0))))
                   (if (logtest mode 2)
                       (progn (%prove (<= (getf prev-info :end-lt) lt) "prev header end_lt > lt")
                              (%prove (>= (getf info :end-lt) lt) "header end_lt < lt"))
                       (progn (%prove (<= (getf prev-info :gen-utime) utime) "prev header gen_utime > utime")
                              (%prove (>= (getf info :gen-utime) utime) "header gen_utime < utime"))))))))
          (list :block-id cur :mc-block alt :info (parse-block-info (svref (cell-refs header) 0))))))))

;;; --- without lookupBlockWithProof ---------------------------------------------------------------
;;;
;;; Mainnet liteservers of older builds answer liteServer.lookupBlockWithProof with "unknown request
;;; type".  Every build knows liteServer.lookupBlock (the block id and its header proof, not tied to any
;;; chain) and liteServer.getShardBlockProof (a chain of Merkle proofs from the masterchain block that
;;; names the shard block, through its ShardHashes, down the previous blocks to the shard block): the
;;; client puts the masterchain block in its trusted chain with getBlockProof (LITE-PROVE-BLOCK).

(defun verify-shard-block-proof (answer block-id)
  "ANSWER, a decoded liteServer.shardBlockProof, for BLOCK-ID (a blockIdExt; masterchain or shard): the
chain of links it carries must start at the masterchain block it names and end exactly at BLOCK-ID.
Returns (:MC-BLOCK the masterchain block id :LINKS the number of links); the caller still has to
place :MC-BLOCK in the chain it trusts."
  (with-proof-errors
    (let ((mc (tl-get answer :masterchain-id))
          (links (coerce (tl-get answer :links) 'list)))
      (%prove (and (= (tl-get mc :workchain) -1) (= (ldb (byte 64 0) (tl-get mc :shard)) (expt 2 63)))
              "shard block proof: the starting block is not of the masterchain")
      (%prove-same-block-id (%verify-shard-link-chain mc links) block-id "shard block proof")
      (list :mc-block mc :links (length links)))))

(defun verify-lookup-header (answer workchain shard mode &key (seqno 0) (lt 0) (utime 0))
  "ANSWER, a decoded liteServer.blockHeader to a plain liteServer.lookupBlock of SHARD of WORKCHAIN in MODE
(seqno, lt or utime bit): the header proof must be a Merkle proof of the answered block's hash whose
BlockInfo agrees with the id, the block must be of the shard asked for, and its seqno (mode 1), end_lt
(mode 2) or gen_utime (mode 4) must not be below the one asked for.  Returns (:BLOCK-ID id :INFO the
BlockInfo :PREV the previous blocks' plists of a lt or utime lookup, whose newest header must still
be checked by VERIFY-LOOKUP-PREV-HEADER).  Nothing here places the block in a chain."
  (with-proof-errors
    (%prove (member (logand mode 7) '(1 2 4)) "lookup mode ~D: exactly one of the seqno, lt, utime bits" mode)
    (let ((id (tl-get answer :id)))
      (%prove (and (= (tl-get id :workchain) workchain) (%shard-id-contains-p (tl-get id :shard) shard))
              "the response block has another workchain or shard than asked for")
      (let* ((header (handler-case
                         (verify-merkle-proof (%single-root (tl-get answer :header-proof) "lookup header")
                                              (tl-get id :root-hash))
                       (boc-error (e) (%prove nil "invalid header hash in proof: ~A" e))))
             (info (parse-block-info (svref (cell-refs header) 0))))
        (%prove (and (= (getf info :seqno) (tl-get id :seqno))
                     (= (getf info :workchain) (tl-get id :workchain))
                     (= (getf info :shard) (ldb (byte 64 0) (tl-get id :shard))))
                "lookup header: BlockInfo disagrees with the id")
        (cond ((logtest mode 1) (%prove (= (tl-get id :seqno) seqno) "invalid seqno in proof"))
              ((logtest mode 2) (%prove (>= (getf info :end-lt) lt) "header end_lt < lt"))
              (t (%prove (>= (getf info :gen-utime) utime) "header gen_utime < utime")))
        (list :block-id id :info info
              :prev (and (logtest mode 6) (parse-block-links header id)))))))

(defun verify-lookup-prev-header (answer prev-id mode &key (lt 0) (utime 0))
  "ANSWER, a decoded liteServer.blockHeader for PREV-ID, a previous block named by the proved header of
a lt (MODE 2) or utime lookup: the block before the answered one must end at or before LT, or be
generated at or before UTIME -- so the answered block is the first to reach it.  True, or a PROOF-ERROR."
  (with-proof-errors
    (%prove-same-block-id (tl-get answer :id) prev-id "lookup prev header")
    (let* ((header (handler-case
                       (verify-merkle-proof (%single-root (tl-get answer :header-proof) "lookup prev header")
                                            (tl-get prev-id :root-hash))
                     (boc-error (e) (%prove nil "invalid prev header hash in proof: ~A" e))))
           (info (parse-block-info (svref (cell-refs header) 0))))
      (%prove (and (= (getf info :seqno) (tl-get prev-id :seqno))
                   (= (getf info :workchain) (tl-get prev-id :workchain)))
              "lookup prev header: BlockInfo disagrees with the id")
      (if (logtest mode 2)
          (%prove (<= (getf info :end-lt) lt) "prev header end_lt > lt")
          (%prove (<= (getf info :gen-utime) utime) "prev header gen_utime > utime"))
      t)))

;;; --- getLibrariesWithProof -------------------------------------------------------------------
;;;
;;; liteserver.cpp continue_getLibrariesWithProof and tonlib's check (TonlibClient.cpp get_libraries):
;;; state_proof is the masterchain block's header proof (-> state hash), data_proof the Merkle proof of
;;; the masterchain STATE revealing the libraries dictionary paths of the requested hashes.  The node
;;; answers for the first 16 requested hashes (sorted, de-duplicated); a library that the state lists
;;; MUST be served, one it does not list MUST NOT be.

(defconstant +max-library-depth+ 512)

(defun verify-libraries-with-proof (answer mc-block-id requested &key (mode 1))
  "ANSWER, a decoded liteServer.libraryResultWithProof for the masterchain block MC-BLOCK-ID, to a
request for REQUESTED (hashes, 32 octets each; only the first 16 are answered) in MODE.  Returns a
list of (HASH . CELL) for the published libraries (CELL is NIL when MODE has bit 1, no data)."
  (with-proof-errors
    (%prove (%same-block-id-p (tl-get answer :id) mc-block-id) "the libraries answer is for another block")
    (%prove (eql (tl-get answer :mode) mode) "the libraries answer has another mode than asked for")
    (let* ((state-hash (nth-value 1 (verify-block-proof (%single-root (tl-get answer :state-proof) "libraries state proof")
                                                        mc-block-id)))
           (state (handler-case (verify-merkle-proof (%single-root (tl-get answer :data-proof) "libraries data proof")
                                                     state-hash)
                    (boc-error (e) (%prove nil "libraries data proof: ~A" e))))
           (root (%state-libraries-root state))
           (asked (remove-duplicates (subseq requested 0 (min 16 (length requested))) :test #'equalp))
           (entries (coerce (tl-get answer :result) 'list))
           (found '()))
      (dolist (entry entries)
        (%prove (find (tl-get entry :hash) asked :test #'equalp) "a library that was not asked for")
        (%prove (= 1 (count (tl-get entry :hash) entries :key (lambda (e) (tl-get e :hash)) :test #'equalp))
                "a library served twice"))
      (dolist (hash asked)
        (let ((entry (find hash entries :key (lambda (e) (tl-get e :hash)) :test #'equalp))
              (value (and root (nth-value 0 (dict-lookup root (octets->uint hash) 256)))))
          (if (null value)
              (%prove (null entry) "library ~A is served but the proof shows it is not published" (octets->hex hash))
              (progn
                (%prove (zerop (load-uint value 2)) "a LibDescr that is not shared_lib_descr")
                (%prove (plusp (slice-remaining-refs value)) "a LibDescr without its library cell")
                (%prove (equalp (node-hash-at (aref (cell-refs (slice-cell value)) (slice-ref-pos value)) 0) hash)
                        "the published library does not hash to ~A" (octets->hex hash))
                (%prove entry "library ~A is published but not served" (octets->hex hash))
                (if (logtest mode 2)
                    (progn (%prove (zerop (length (tl-get entry :data))) "library data served although mode asks for none")
                           (push (cons hash nil) found))
                    (let ((cell (%single-root (tl-get entry :data) "library")))
                      (%prove (equalp (node-hash-at cell 0) hash) "a library whose cell hashes to another value")
                      (%prove (<= (node-depth-at cell 0) +max-library-depth+) "a library that is too deep")
                      (push (cons hash cell) found)))))))
      (nreverse found))))
