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

;;;; fakechain.lisp -- Phase F.1: an emulator-backed liteserver, the project's
;;;; simulated network.
;;;;
;;;; It is a real ADNL-ext liteserver (same listener as the proxy uses) whose
;;;; answers come from a local chain model.  State transitions are produced BY
;;;; the TVM emulator (libemulator): sendMessage queues an external message;
;;;; each tick of the virtual clock emulates queued messages against their
;;;; destination ShardAccount, records the resulting Transaction cell, feeds
;;;; outbound internal messages back into the queue, and seals a
;;;; masterchain + workchain-0 block pair.
;;;;
;;;; tonlib VERIFIES what a liteserver tells it (Merkle proofs, block header
;;;; proofs, validator signatures), so the model is a small but genuine chain:
;;;;   * a zero state whose ConfigParams carry OUR validator set (param 34);
;;;;   * blocks (BlockInfo, ValueFlow, MERKLE_UPDATE state_update, BlockExtra)
;;;;     whose masterchain ids are signed by that validator (forward proof
;;;;     links from the zero state, as liteServer.getBlockProof answers);
;;;;   * ShardStateUnsplit cells with real ShardAccounts hashmaps, so
;;;;     getAccountState carries a shard proof (mc state -> shard block) and an
;;;;     account proof (shard block -> state -> account) tonlib accepts.
;;;; Proof cells are built UNPRUNED (whole trees under the Merkle proof
;;;; cell): the states are small, and it keeps every cell level-0 so cl-ton's
;;;; ordinary cell hashing is exactly the representation hash.
;;;;
;;;; Contracts are whatever code/data the test seeds (FAKECHAIN-SET-ACCOUNT);
;;;; the repository carries no DEX pool code, so seeding real router/pool
;;;; cells captured from a live network is the caller's job.

(in-package :cl-ton)

;;; ---------------------------------------------------------------------------
;;; TL-B builders
;;; ---------------------------------------------------------------------------

(defconstant +fake-global-id+ -239)
(defparameter +fc-validator-seed+
  (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x5a)
  "Seed of the fakechain's masterchain validator.  Public and test-only by design.")
(defparameter +fc-validator-set-hash+ 1234420764
  "gen_validator_list_hash_short of a masterchain block (cc_seqno 0) for the fixed
validator set; tonlib recomputes it and compares.")
(defconstant +mc-shard+ #x8000000000000000)

(defun %hash->int (octets) (octets->uint octets))
(defun %store-hash (b octets) (store-uint b (%hash->int octets) 256))

(defun %store-cc (b &optional (coins 0))
  "CurrencyCollection: Grams + empty ExtraCurrencyCollection."
  (store-bit (store-coins b coins) 0))

(defun %store-shard-ident (b workchain shard)
  "shard_ident$00 shard_pfx_bits:(#<= 60) workchain_id:int32 shard_prefix:uint64"
  ;; SHARD carries the tag bit (0x8000... = whole workchain); the wire form stores
  ;; the prefix with that lowest set bit CLEARED (a whole workchain is prefix 0).
  (let* ((u (ldb (byte 64 0) shard))
         (low (if (zerop u) 0 (loop for i from 0 below 64 when (logbitp i u) return i)))
         (pfx (if (zerop u) 0 (- 63 low)))
         (prefix (if (zerop u) 0 (logandc2 u (ash 1 low)))))
    (store-uint (store-int (store-uint (store-uint b 0 2) pfx 6) workchain 32) prefix 64)))

(defun %store-ext-blk-ref (b end-lt seqno root-hash file-hash)
  (%store-hash (%store-hash (store-uint (store-uint b end-lt 64) seqno 32) root-hash) file-hash))

(defun %empty-depth-balance-aug (b)
  "extra of an empty HashmapAugE with DepthBalanceInfo: split_depth(5) + CC."
  (%store-cc (store-uint b 0 5)))

(defun %empty-accounts-cell ()
  (end-cell (%empty-depth-balance-aug (store-bit (begin-cell) 0))))

(defun %exotic-cell (bits nbits refs)
  (make-cell :bits bits :bit-length nbits :refs refs :exotic t))

(defun make-merkle-proof (node)
  "MerkleProof exotic cell over NODE (level-0 tree, unpruned)."
  (%exotic-cell (logior (ash 3 272) (ash (%hash->int (node-hash node)) 16) (node-depth node))
                (+ 8 256 16) (list node)))

(defun make-merkle-update (old new)
  "MerkleUpdate: type 4, old_hash, new_hash, old_depth, new_depth."
  (let ((bits (logior (ash 4 (+ 256 256 16 16))
                      (ash (%hash->int (node-hash old)) (+ 256 16 16))
                      (ash (%hash->int (node-hash new)) (+ 16 16))
                      (ash (node-depth old) 16)
                      (node-depth new))))
    (%exotic-cell bits (+ 8 256 256 16 16) (list old new))))

(defun boc-of (&rest roots)
  (serialize-boc roots :has-crc32c nil))

;;; --- HashmapAugE 256 ShardAccount DepthBalanceInfo ----------------------------

(defun %store-depth-balance (b depth coins)
  (%store-cc (store-uint b depth 5) coins))

(defun %account-balance (shard-account)
  "Balance in nanoTON of a ShardAccount cell (0 for account_none)."
  (let* ((acc (first-ref-cell shard-account))
         (s (cell-slice acc)))
    (multiple-value-bind (tag s1) (load-uint s 1)
      (if (zerop tag)
          0
          (progn
            (setf s s1)
            ;; addr, storage_stat (StorageInfo), then last_trans_lt, balance
            (setf s (%skip-msg-address s))
            (setf s (%skip-storage-info s))
            (multiple-value-bind (lt s2) (load-uint s 64)
              (declare (ignore lt))
              (multiple-value-bind (coins s3) (load-coins s2)
                (declare (ignore s3))
                coins)))))))

(defun first-ref-cell (cell)
  (aref (cell-refs cell) 0))

(defun %skip-msg-address (s)
  "Skip an addr_std (or addr_none) MsgAddressInt at the head of S."
  (multiple-value-bind (tag s1) (load-uint s 2)
    (case tag
      (0 s1)
      (2 (multiple-value-bind (anycast s2) (load-uint s1 1)
           (declare (ignore anycast))
           (skip-bits s2 (+ 8 256))))
      (t (ton-error "unsupported address tag ~D in account" tag)))))

(defun %skip-varuint (s len-bits)
  (multiple-value-bind (n s1) (load-uint s len-bits)
    (skip-bits s1 (* 8 n))))

(defun %skip-storage-info (s)
  ;; storage_used$_ cells:(VarUInteger 7) bits:(VarUInteger 7) ; storage_extra ; last_paid:uint32 ; due_payment:(Maybe Grams)
  (let* ((s (%skip-varuint s 3))
         (s (%skip-varuint s 3)))
    (multiple-value-bind (extra s1) (load-uint s 3)   ; storage_extra_none$000 / info$001 (+256)
      (let ((s (if (= extra 1) (skip-bits s1 256) s1)))
        (let ((s (skip-bits s 32)))
          (multiple-value-bind (has-due s1) (load-uint s 1)
            (if (= has-due 1) (%skip-varuint s1 4) s1)))))))

(defun %safe-balance (shard-account)
  (handler-case (%account-balance shard-account) (error () 0)))

(defun build-shard-accounts (entries)
  "ENTRIES: list of (ACCOUNT-HASH-INTEGER . SHARD-ACCOUNT-CELL), keys distinct.
Returns (VALUES ROOT-CELL TOTAL-BALANCE): HashmapAugE 256 ShardAccount
DepthBalanceInfo with genuine aggregated augmentation."
  (if (null entries)
      (values (%empty-accounts-cell) 0)
      (labels ((total (es) (reduce #'+ es :key (lambda (e) (%safe-balance (cdr e)))))
               (build (es n)
                 ;; -> (VALUES cell depth)
                 (let* ((first-key (car (first es)))
                        (prefix-len (loop for l from 0 below n
                                          while (every (lambda (e)
                                                         (= (ldb (byte 1 (- n l 1)) (car e))
                                                            (ldb (byte 1 (- n l 1)) first-key)))
                                                       es)
                                          count t))
                        (label (ldb (byte prefix-len (- n prefix-len)) first-key))
                        (m (- n prefix-len))
                        (b (store-hm-label (begin-cell) label prefix-len n)))
                   (if (zerop m)
                       (values (end-cell (store-builder (%store-depth-balance b 0 (total es))
                                                        (cell->builder (cdr (first es)))))
                               0)
                       (let* ((bit (1- m))
                              (left (remove-if (lambda (e) (logbitp bit (car e))) es))
                              (right (remove-if-not (lambda (e) (logbitp bit (car e))) es)))
                         (multiple-value-bind (lcell ld) (build left (1- m))
                           (multiple-value-bind (rcell rd) (build right (1- m))
                             (let ((depth (min 30 (1+ (max ld rd)))))
                               (values (end-cell (store-ref (store-ref (%store-depth-balance b depth (total es))
                                                                       lcell)
                                                            rcell))
                                       depth)))))))))
        (multiple-value-bind (root depth) (build entries 256)
          (values (end-cell (store-ref (%store-depth-balance (store-bit (begin-cell) 1) depth (total entries))
                                       root))
                  (total entries))))))

;;; ---------------------------------------------------------------------------
;;; ConfigParams
;;; ---------------------------------------------------------------------------

(defun %param (fn) (end-cell (funcall fn (begin-cell))))

(defun %addr-param (octets) (%param (lambda (b) (%store-hash b octets))))

(defun %gas-prices-cell (&key flat-limit flat-price price (limit 1000000) (special 100000000)
                           (credit 10000) (block-limit 10000000) (freeze 100000000) (delete 1000000000))
  (%param (lambda (b)
            (let* ((b (store-uint b #xd1 8))
                   (b (store-uint b flat-limit 64))
                   (b (store-uint b flat-price 64))
                   (b (store-uint b #xde 8)))
              (dolist (v (list price limit special credit block-limit freeze delete) b)
                (setf b (store-uint b v 64)))))))

(defun %msg-prices-cell (&key lump bit cell)
  (%param (lambda (b)
            (let* ((b (store-uint b #xea 8)) (b (store-uint b lump 64)) (b (store-uint b bit 64))
                   (b (store-uint b cell 64)) (b (store-uint b 98304 32))
                   (b (store-uint b 21845 16)))
              (store-uint b 21845 16)))))

(defun %param-limits (b underload soft hard)
  (store-uint (store-uint (store-uint (store-uint b #xc3 8) underload 32) soft 32) hard 32))

(defun %block-limits-cell (bytes gas lt)
  (%param (lambda (b)
            (let ((b (store-uint b #x5d 8)))
              (%param-limits (%param-limits (%param-limits b (first bytes) (second bytes) (third bytes))
                                            (first gas) (second gas) (third gas))
                             (first lt) (second lt) (third lt))))))

(defun %validators-cell (public-key since until)
  "validators_ext#12 with a single validator of weight 1."
  (%param (lambda (b)
            (let* ((b (store-uint b #x12 8))
                   (b (store-uint b since 32)) (b (store-uint b until 32))
                   (b (store-uint b 1 16)) (b (store-uint b 1 16))
                   (b (store-uint b 1 64)))
              (store-dict b (list (cons 0 (lambda (vb)
                                            (store-uint (%store-hash (store-uint (store-uint vb #x53 8) #x8e81278a 32) public-key)
                                                    1 64))))
                          16)))))

(defun build-fake-config (validator-public &key (utime-since 0) (utime-until #xffffffff)
                                              (config-addr (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x55)))
  "The ConfigParams dictionary root (Hashmap 32 ^Cell) for the fake chain."
  (let* ((entries
           (list
            ;; param 0 is REQUIRED by libemulator ("Can't find config address (param 0)")
            (cons 0 (%addr-param config-addr))
            (cons 1 (%addr-param (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x33)))
            (cons 2 (%addr-param (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x22)))
            (cons 4 (%addr-param (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x44)))
            (cons 8 (%param (lambda (b) (store-uint (store-uint (store-uint b #xc4 8) 9 32)
                                                    (logior 4 8 128 256 512 1024 2048) 64))))
            (cons 9 (%param (lambda (b) (store-builder b (cell->builder (hashmap-cell (list (cons 0 #'identity)
                                                                                           (cons 8 #'identity)
                                                                                           (cons 9 #'identity))
                                                                                     32))))))
            (cons 12 (%param (lambda (b)
                               (store-dict b (list (cons 0 (lambda (vb)
                                                             (let* ((vb (store-uint vb #xa6 8))
                                                                    (vb (store-uint vb 0 32))
                                                                    (vb (store-uint vb 0 8)) (vb (store-uint vb 0 8))
                                                                    (vb (store-uint vb 0 8))
                                                                    (vb (store-uint vb 1 1)) (vb (store-uint vb 1 1))
                                                                    (vb (store-uint vb 1 1)) (vb (store-uint vb 0 13))
                                                                    (vb (store-uint vb 0 256)) (vb (store-uint vb 0 256))
                                                                    (vb (store-uint vb 0 32)))
                                                               (store-uint (store-uint (store-uint vb 1 4) 0 32) 0 64)))))
                                           32))))
            (cons 14 (%param (lambda (b) (store-coins (store-coins (store-uint b #x6b 8) 1700000000) 1000000000))))
            (cons 15 (%param (lambda (b) (dolist (v '(65536 32768 8192 32768) b)
                                           (setf b (store-uint b v 32))))))
            (cons 16 (%param (lambda (b) (store-uint (store-uint (store-uint b 1000 16) 100 16) 1 16))))
            (cons 17 (%param (lambda (b) (store-uint (store-coins (store-coins (store-coins b 10000000000000) 10000000000000000) 10000000000000) 3 32))))
            (cons 18 (hashmap-cell (list (cons 0 (lambda (vb)
                                                   (let* ((vb (store-uint vb #xcc 8)) (vb (store-uint vb 0 32)))
                                                     (dolist (v '(1 500 1000 500000) vb)
                                                       (setf vb (store-uint vb v 64)))))))
                                   32))
            (cons 20 (%gas-prices-cell :flat-limit 100 :flat-price 10000000 :price 655360000))
            (cons 21 (%gas-prices-cell :flat-limit 100 :flat-price 1000000 :price 65536000))
            (cons 22 (%block-limits-cell '(131072 524288 1048576) '(200000 900000 1000000) '(1000 5000 10000)))
            (cons 23 (%block-limits-cell '(131072 524288 1048576) '(200000 900000 1000000) '(1000 5000 10000)))
            (cons 24 (%msg-prices-cell :lump 10000000 :bit 655360000 :cell 65536000000))
            (cons 25 (%msg-prices-cell :lump 400000 :bit 26214400 :cell 2621440000))
            (cons 28 (%param (lambda (b) (let ((b (store-uint b #xc1 8)))
                                           (dolist (v '(25 25 25 8) b) (setf b (store-uint b v 32)))))))
            (cons 31 (%param (lambda (b) (store-dict b '() 256))))
            (cons 34 (%validators-cell validator-public utime-since utime-until)))))
    (hashmap-cell (mapcar (lambda (e) (cons (car e) (let ((c (cdr e))) (lambda (b) (store-ref b c)))))
                          (sort entries #'< :key #'car))
                  32)))

;;; ---------------------------------------------------------------------------
;;; The chain model
;;; ---------------------------------------------------------------------------

(defstruct (fc-block (:copier nil))
  seqno utime start-lt end-lt
  mc-block mc-state mc-root mc-file
  sh-block sh-state sh-root sh-file
  signature accounts)

(defstruct (fakechain (:constructor %make-fakechain) (:copier nil))
  keypair                               ; the liteserver's ADNL identity
  validator                             ; ed25519 keypair signing masterchain blocks
  config                                ; ConfigParams dictionary root cell
  config-addr
  zero-state zero-root zero-file
  wc0-zero-state wc0-zero-root wc0-zero-file
  (accounts (make-hash-table))          ; account-hash integer -> ShardAccount cell
  (txs (make-hash-table))               ; account-hash integer -> list of (tx-cell . block-index), newest first
  (blocks (make-array 0 :adjustable t :fill-pointer t))
  (queue '())                           ; messages awaiting the next tick, oldest first
  (lock (sb-thread:make-mutex :name "fakechain"))
  server ticker
  (time-mode :manual) (clock 0) (tick-seconds 3) (tick-interval 1)
  (lt 1000000)
  (max-messages-per-tick 256)
  (drop-externals 0)                    ; fault injection: silently drop the next N accepted externals
  (stall-p nil)                         ; fault injection: blocks stop being produced
  (answer-delay 0)                      ; fault injection: seconds every query waits before it is processed
  (fail-next 0)                         ; fault injection: the next N queries get liteServer.error 502
  (libraries '())                       ; alist (hash-hex . cell): on-chain library cells (masterchain libraries)
  (lagging-p nil)                       ; fault injection: a server whose shard client lags -- everything but
                                        ; getMasterchainInfo answers liteServer.error 651 "block is not in db"
  (log '())
  (stopped nil)
  (extra-handlers '()))

(defun fc-lock-call (fc thunk)
  (sb-thread:with-recursive-lock ((fakechain-lock fc)) (funcall thunk)))

(defmacro with-fc-lock ((fc) &body body)
  `(fc-lock-call ,fc (lambda () ,@body)))

(defun fc-address-key (addr)
  "Integer key of an ADDRESS (workchain 0 only carries accounts here)."
  (octets->uint (address-hash addr)))

(defun fc-now (fc) (fakechain-clock fc))

(defun fc-head (fc)
  "Newest FC-BLOCK, or NIL before the first tick."
  (let ((blocks (fakechain-blocks fc)))
    (and (plusp (length blocks)) (aref blocks (1- (length blocks))))))

(defun fc-head-seqno (fc)
  (let ((h (fc-head fc))) (if h (fc-block-seqno h) 0)))

;;; --- ShardAccount helpers -------------------------------------------------------

(defun fc-empty-shard-account ()
  "ShardAccount of a nonexistent account."
  (build-cell (store-ref (end-cell (store-bit (begin-cell) 0)))
              (store-uint 0 256) (store-uint 0 64)))

(defun fc-shard-account (fc addr)
  (or (gethash (fc-address-key addr) (fakechain-accounts fc))
      (fc-empty-shard-account)))

;;; Libraries: contracts whose code (or deployed children's code) is a LIBRARY CELL --
;;; STON.fi v2 keeps pool / LP-account / vault code that way -- only execute when the
;;; emulator is given the referenced code.  The fakechain keeps them like the masterchain's
;;; library collection: the emulator gets all of them for every transaction, and direct ADNL
;;; clients can fetch them through liteServer.getLibraries.  (tonlib itself asks with the
;;; proof-checked getLibrariesWithProof, which this fake chain cannot answer.)
(defun fakechain-add-library (fc code-cell)
  "Publish CODE-CELL as a library (keyed by its hash); returns the lower-case hex hash."
  (let ((hex (string-downcase (cell-hash-hex code-cell))))
    (with-fc-lock (fc)
      (unless (assoc hex (fakechain-libraries fc) :test #'string=)
        (push (cons hex code-cell) (fakechain-libraries fc))))
    hex))

(defun fc-answer-get-libraries (fc fn)
  "liteServer.getLibraries: the requested libraries this chain has (absent ones are omitted)."
  (let ((libs (with-fc-lock (fc) (copy-list (fakechain-libraries fc)))))
    (tl-encode
     (tl-make "liteServer.libraryResult"
              :result (loop for h in (coerce (tl-get fn :library-list) 'list)
                            for e = (assoc (string-downcase (octets->hex h)) libs :test #'string=)
                            when e
                              collect (tl-make "liteServer.libraryEntry" :hash h
                                                                         :data (serialize-boc (cdr e))))))))

(defun fakechain-set-account (fc addr &key code data (balance 0) state-init)
  "Seed (or replace) the account at ADDR as an ACTIVE contract with CODE/DATA and
BALANCE nanoTON.  STATE-INIT overrides CODE/DATA when given."
  (with-fc-lock (fc)
    (let* ((si (or state-init (make-state-init code data)))
           (sa (funded-shard-account addr si balance)))
      (setf (gethash (fc-address-key addr) (fakechain-accounts fc)) sa)
      sa)))

(defun fakechain-set-shard-account (fc addr shard-account)
  (with-fc-lock (fc)
    (setf (gethash (fc-address-key addr) (fakechain-accounts fc)) shard-account)))

(defun fakechain-account-balance (fc addr)
  (%safe-balance (fc-shard-account fc addr)))

;;; --- states --------------------------------------------------------------------

(defun %out-msg-queue-info-cell ()
  (end-cell (store-bit (store-bit (store-uint (store-bit (begin-cell) 0) 0 64) 0) 0)))

(defun %shard-descr (b &key seqno reg-mc-seqno start-lt end-lt root-hash file-hash gen-utime)
  (let* ((b (store-uint b #xb 4))
         (b (store-uint b seqno 32)) (b (store-uint b reg-mc-seqno 32))
         (b (store-uint b start-lt 64)) (b (store-uint b end-lt 64))
         (b (%store-hash b root-hash)) (b (%store-hash b file-hash))
         (b (store-uint b 0 5)) (b (store-uint b 0 3))
         (b (store-uint b 0 32)) (b (store-uint b +mc-shard+ 64))
         (b (store-uint b 0 32)) (b (store-uint b gen-utime 32))
         (b (store-bit b 0)))
    (%store-cc (%store-cc b) 0)))

(defun %bt-leaf (&rest descr-args)
  (end-cell (apply #'%shard-descr (store-bit (begin-cell) 0) descr-args)))

(defun build-shard-state (&key workchain shard seqno utime lt accounts-root total master-ref custom)
  "ShardStateUnsplit."
  (let* ((b (begin-cell))
         (b (store-uint b #x9023afe2 32))
         (b (store-int b +fake-global-id+ 32))
         (b (%store-shard-ident b workchain shard))
         (b (store-uint b seqno 32)) (b (store-uint b 0 32))
         (b (store-uint b utime 32)) (b (store-uint b lt 64))
         (b (store-uint b 0 32))
         (b (store-ref b (%out-msg-queue-info-cell)))
         (b (store-bit b 0))
         (b (store-ref b accounts-root))
         (tail (let* ((tb (begin-cell))
                      (tb (store-uint tb 0 64)) (tb (store-uint tb 0 64))
                      (tb (%store-cc tb total)) (tb (%store-cc tb 0))
                      (tb (store-bit tb 0)))
                 (end-cell (if master-ref
                               (destructuring-bind (end-lt seqno root file) master-ref
                                 (%store-ext-blk-ref (store-bit tb 1) end-lt seqno root file))
                               (store-bit tb 0)))))
         (b (store-ref b tail)))
    (end-cell (if custom
                  (store-ref (store-bit b 1) custom)
                  (store-bit b 0)))))

(defun %old-mc-blocks-dict (entries)
  "HashmapAugE 32 KeyExtBlkRef KeyMaxLt over ENTRIES = list of (SEQNO END-LT ROOT FILE)
(none a key block).  (VALUES ROOT-CELL MAX-END-LT); the per-node extra is
KeyMaxLt = key:Bool(0) max_end_lt:uint64 aggregated as the max over the subtree."
  (labels ((build (es n)
             (let* ((first-key (first (first es)))
                    (prefix-len (loop for l from 0 below n
                                      while (every (lambda (e) (= (ldb (byte 1 (- n l 1)) (first e))
                                                                  (ldb (byte 1 (- n l 1)) first-key)))
                                                   es)
                                      count t))
                    (label (ldb (byte prefix-len (- n prefix-len)) first-key))
                    (m (- n prefix-len))
                    (max-lt (reduce #'max es :key #'second))
                    (any-key (if (some (lambda (e) (eql (fifth e) 1)) es) 1 0))
                    (b (store-hm-label (begin-cell) label prefix-len n))
                    (b (store-uint b (logior (ash any-key 64) max-lt) 65)))   ; extra: key:Bool max_end_lt:uint64
               (if (zerop m)
                   (destructuring-bind (seqno end-lt root file &optional (key 0)) (first es)
                     ;; value: KeyExtBlkRef = key:Bool blk_ref:ExtBlkRef
                     (end-cell (%store-ext-blk-ref (store-bit b key) end-lt seqno root file)))
                   (let* ((bit (1- m))
                          (left (remove-if (lambda (e) (logbitp bit (first e))) es))
                          (right (remove-if-not (lambda (e) (logbitp bit (first e))) es)))
                     (end-cell (store-ref (store-ref b (build left (1- m))) (build right (1- m)))))))))
    (values (build entries 32) (reduce #'max entries :key #'second)
            (if (some (lambda (e) (eql (fifth e) 1)) entries) 1 0))))

(defun build-mc-state-extra (&key shard-entries config-dict config-addr old-blocks)
  "McStateExtra.  SHARD-ENTRIES: list of (WORKCHAIN . BT-LEAF-CELL)."
  (let* ((b (store-uint (begin-cell) #xcc26 16))
         (b (store-dict b (mapcar (lambda (e) (cons (car e) (let ((c (cdr e))) (lambda (vb) (store-ref vb c)))))
                                  shard-entries)
                        32))
         (b (%store-hash b config-addr))
         (b (store-ref b config-dict)))
    ;; ^[ flags:(## 16) validator_info:ValidatorInfo prev_blocks:OldMcBlocksInfo
    ;;    after_key_block:Bool last_key_block:(Maybe ExtBlkRef) ]
    (let* ((mb (store-uint (begin-cell) 0 16))
           (mb (store-bit (store-uint (store-uint mb 0 32) 0 32) 0))       ; validator_info$_ hash catchain nx_cc_updated
           ;; prev_blocks:OldMcBlocksInfo = HashmapAugE 32 KeyExtBlkRef KeyMaxLt, one entry per earlier
           ;; masterchain block (incl. the zero state at key 0); OLD-BLOCKS = list of (SEQNO END-LT ROOT FILE).
           (mb (if old-blocks
                   (multiple-value-bind (root max-lt any-key) (%old-mc-blocks-dict old-blocks)
                     (store-uint (store-ref (store-bit mb 1) root) (logior (ash any-key 64) max-lt) 65))  ; hme_root + ^root + extra(key=0, max_end_lt)
                   (store-uint (store-bit mb 0) 0 65)))                          ; ahme_empty + extra
           (mb (store-bit mb 0))                                           ; after_key_block
           ;; last_key_block:(Maybe ExtBlkRef): the zero state is the (only) key block
           (mb (let ((zero (find 0 old-blocks :key #'first)))
                 (if zero
                     (%store-ext-blk-ref (store-bit mb 1) (second zero) 0 (third zero) (fourth zero))
                     (store-bit mb 0)))))
      (end-cell (%store-cc (store-ref b (end-cell mb)) 0)))))

;;; --- Merkle update (unpruned: both trees kept whole, every cell level 0) ---------

(defun make-state-update (old new)
  "MERKLE_UPDATE (exotic type 4) from OLD to NEW state roots."
  (make-merkle-update old new))

;;; --- blocks ----------------------------------------------------------------------

(defun %block-info-cell (&key not-master seqno workchain shard utime start-lt end-lt
                           prev-ref master-ref)
  "PREV-REF / MASTER-REF: (END-LT SEQNO ROOT FILE)."
  (let* ((b (store-uint (begin-cell) #x9bc7a987 32))
         (b (store-uint b 0 32))
         (b (store-uint b (if not-master 1 0) 1))
         (b (store-uint b 0 3))                         ; after_merge before_split after_split
         (b (store-uint b 0 4))                         ; want_split want_merge key_block vert_seqno_incr
         (b (store-uint b 0 8))                         ; flags
         (b (store-uint b seqno 32)) (b (store-uint b 0 32))
         (b (%store-shard-ident b workchain shard))
         (b (store-uint b utime 32))
         (b (store-uint b start-lt 64)) (b (store-uint b end-lt 64))
         (b (store-uint b (if not-master 0 +fc-validator-set-hash+) 32)) ; gen_validator_list_hash_short
         (b (store-uint b 0 32))                                          ; gen_catchain_seqno
         (b (store-uint b 0 32)) (b (store-uint b 0 32)))                 ; min_ref_mc_seqno prev_key_block_seqno
    (when not-master
      (setf b (store-ref b (end-cell (apply #'%store-ext-blk-ref (begin-cell) master-ref)))))
    (setf b (store-ref b (end-cell (apply #'%store-ext-blk-ref (begin-cell) prev-ref))))
    (end-cell b)))

(defun %value-flow-cell ()
  (let* ((a (end-cell (%store-cc (%store-cc (%store-cc (%store-cc (begin-cell) 0) 0) 0) 0)))
         (b (end-cell (%store-cc (%store-cc (%store-cc (%store-cc (begin-cell) 0) 0) 0) 0))))
    (end-cell (store-ref (store-ref (%store-cc (store-uint (begin-cell) #xb8e48dfb 32) 0) a) b))))

(defun %block-extra-cell (utime)
  (let* ((in (end-cell (store-builder (store-bit (begin-cell) 0) (cell->builder (end-cell (%store-cc (store-coins (begin-cell) 0) 0))))))
         (out (end-cell (%store-cc (store-bit (begin-cell) 0) 0)))
         (acc (end-cell (%store-cc (store-bit (begin-cell) 0) 0)))
         (seed (sha256 (uint->octets utime 4))))
    (end-cell (store-uint (%store-hash (%store-hash (store-uint (store-ref (store-ref (store-ref (store-uint (begin-cell) #x4a33f6fd 32) in) out) acc)
                                                                0 0)
                                                    seed)
                                       seed)
                          0 1))))

(defun build-block (&key info state-update utime)
  (end-cell (store-ref (store-ref (store-ref (store-ref (store-int (store-uint (begin-cell) #x11ef55aa 32)
                                                                   +fake-global-id+ 32)
                                                        info)
                                             (%value-flow-cell))
                                  state-update)
                       (%block-extra-cell utime))))

(defun %file-hash (cell) (sha256 (boc-of cell)))

(defun %ext-ref (end-lt seqno root file) (list end-lt seqno root file))

;;; --- genesis --------------------------------------------------------------------

(defun %shard-leaf-for (&key seqno reg-mc start-lt end-lt root file utime)
  (%bt-leaf :seqno seqno :reg-mc-seqno reg-mc :start-lt start-lt :end-lt end-lt
            :root-hash root :file-hash file :gen-utime utime))

(defun %mc-state (fc &key seqno utime lt wc0-leaf master-ref)
  (declare (ignore master-ref))
  (build-shard-state :workchain -1 :shard +mc-shard+ :seqno seqno :utime utime :lt lt
                     :accounts-root (%empty-accounts-cell) :total 0
                     :custom (build-mc-state-extra :shard-entries (list (cons 0 wc0-leaf))
                                                   :config-dict (fakechain-config fc)
                                                   :config-addr (fakechain-config-addr fc)
                                                   :old-blocks (and (plusp seqno) (fakechain-zero-root fc)
                                                                    (cons (list 0 0 (fakechain-zero-root fc)
                                                                                (fakechain-zero-file fc) 1)
                                                                          (loop for b across (fakechain-blocks fc)
                                                                                when (< (fc-block-seqno b) seqno)
                                                                                  collect (list (fc-block-seqno b)
                                                                                                (fc-block-end-lt b)
                                                                                                (fc-block-mc-root b)
                                                                                                (fc-block-mc-file b))))))))

(defun fakechain-init (fc)
  "Build the zero states (masterchain with the validator config, workchain 0
empty) and seal block 1 so tonlib always finds a real block to sync to."
  (let* ((utime (fc-now fc))
         (wc0-zero (build-shard-state :workchain 0 :shard +mc-shard+ :seqno 0 :utime utime :lt 0
                                      :accounts-root (%empty-accounts-cell) :total 0))
         (wc0-file (%file-hash wc0-zero))
         (leaf (%shard-leaf-for :seqno 0 :reg-mc 0 :start-lt 0 :end-lt 0
                                :root (node-hash wc0-zero) :file wc0-file :utime utime))
         (zero (%mc-state fc :seqno 0 :utime utime :lt 0 :wc0-leaf leaf)))
    (setf (fakechain-wc0-zero-state fc) wc0-zero
          (fakechain-wc0-zero-root fc) (node-hash wc0-zero)
          (fakechain-wc0-zero-file fc) wc0-file
          (fakechain-zero-state fc) zero
          (fakechain-zero-root fc) (node-hash zero)
          (fakechain-zero-file fc) (%file-hash zero))
    (fakechain-tick fc)
    fc))

(defun make-fakechain (&key (seed-time (unix-now)) (time-mode :manual) (tick-seconds 3)
                         (tick-interval 1) (identity-seed nil))
  "A fresh fake chain, not yet listening (see START-FAKECHAIN)."
  (unless *emulator-loaded*
    ;; the default "../lib/..." only resolves in a deployed layout; in a checkout
    ;; use the library next to the system.
    (let ((p (ignore-errors (asdf:system-relative-pathname "cl-ton" "lib/libemulator-linux-x86_64.so"))))
      (if (and p (probe-file p))
          (load-emulator-library (namestring p))
          (load-emulator-library))))
  (let* ((kp (if identity-seed (seed->keypair identity-seed) (adnl-generate-keypair)))
         ;; A FIXED (public, test-only) validator key: the validator-set hash tonlib
         ;; checks in every masterchain header depends on the key, so a constant key
         ;; makes it a constant (+FC-VALIDATOR-SET-HASH+), observed from tonlib itself.
         (validator (seed->keypair +fc-validator-seed+))
         (fc (%make-fakechain :keypair kp :validator validator :clock seed-time
                              :time-mode time-mode :tick-seconds tick-seconds :tick-interval tick-interval
                              :config-addr (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x55))))
    (setf (fakechain-config fc) (build-fake-config (keypair-public validator)))
    (fakechain-init fc)))

;;; --- ticking: emulate queued messages, seal a block pair ---------------------------

(defun fc-shard-account-none-p (shard-account)
  "True when SHARD-ACCOUNT's Account is account_none$0."
  (zerop (cell-uint (first-ref-cell shard-account) 0 1)))

(defun fc-log (fc &rest entry) (push entry (fakechain-log fc)))

(defun fc-next-lt (fc) (incf (fakechain-lt fc) 1000))

(defun fc-emulate-one (fc msg)
  "Route MSG by kind and emulate it against its destination account.
 external-in / internal to workchain 0 -> real libemulator transaction
 external-out                           -> recorded in the log, not delivered
 anything else                          -> recorded in the log and dropped
Every transaction gets a fresh, monotonically increasing lt so transaction
and block ranges agree.  Returns (VALUES tx-cell dest-address out-messages);
bounces, refunds and chained hops are just out-messages that re-enter the queue."
  (let ((header (handler-case (parse-message-header msg) (error () nil))))
    (when (null header)
      (fc-log fc :unparseable-message)
      (return-from fc-emulate-one (values nil nil nil)))
    (when (eq (getf header :type) :external-out)
      (fc-log fc :external-out msg)
      (return-from fc-emulate-one (values nil nil nil)))
    (let ((dest (getf header :dest)))
      (unless (and dest (eql (address-workchain dest) 0))
        (fc-log fc :undeliverable (getf header :type) dest)
        (return-from fc-emulate-one (values nil nil nil)))
      (let* ((lt (fc-next-lt fc))
             (r (emulate-message (fakechain-config-full fc) (fc-shard-account fc dest) msg
                                 :libraries (fakechain-libraries fc)
                                 :unixtime (fc-now fc) :ignore-chksig nil :lt lt
                                 :rand-seed (octets->hex (sha256 (uint->octets lt 8))))))
        (cond ((emulation-result-success-p r)
               ;; Like a real shard, forget accounts that do not exist after the
               ;; transaction (a bounced message to a never-deployed address):
               ;; they are absent from ShardAccounts, and tonlib's proof check
               ;; rejects an entry whose Account is account_none.
               (if (fc-shard-account-none-p (emulation-result-shard-account r))
                   (remhash (fc-address-key dest) (fakechain-accounts fc))
                   (setf (gethash (fc-address-key dest) (fakechain-accounts fc))
                         (emulation-result-shard-account r)))
               (values (emulation-result-transaction r) dest
                       (nth-value 1 (transaction-messages (emulation-result-transaction r)))))
              (t (fc-log fc :emulation-failed (getf header :type) (emulation-result-error r))
                 (values nil nil nil)))))))

(defun fakechain-config-full (fc)
  "The config in the shape libemulator wants: the ConfigParams dictionary root."
  (fakechain-config fc))

(defun fc-tick-messages (fc)
  "Drain (up to the per-tick cap of) the queue; returns the list of
(TX . ADDR) processed.  Outbound internal messages re-enter the queue."
  (let ((done '()) (n 0) (out-of-round '()))
    (loop while (and (fakechain-queue fc) (< n (fakechain-max-messages-per-tick fc)))
          do (let ((msg (pop (fakechain-queue fc))))
               (incf n)
               (multiple-value-bind (tx dest outs) (fc-emulate-one fc msg)
                 (when tx
                   (push (cons tx dest) done)
                   (dolist (o outs) (push o out-of-round))))))
    (setf (fakechain-queue fc) (append (fakechain-queue fc) (nreverse out-of-round)))
    (nreverse done)))

(defun fc-accounts-root (fc)
  (build-shard-accounts
   (loop for k being the hash-keys of (fakechain-accounts fc) using (hash-value sa)
         collect (cons k sa) into l
         finally (return (sort l #'< :key #'car)))))

(defun fc-seal-block (fc processed)
  (let* ((seqno (1+ (fc-head-seqno fc)))
         (prev (fc-head fc))
         (utime (incf (fakechain-clock fc) (fakechain-tick-seconds fc)))
         (start-lt (if prev (fc-block-end-lt prev) 0))
         (end-lt (+ (fakechain-lt fc) (length processed) 1))
         (accounts-root (fc-accounts-root fc))
         (old-wc0 (if prev (fc-block-sh-state prev) (fakechain-wc0-zero-state fc)))
         (new-wc0 (build-shard-state :workchain 0 :shard +mc-shard+ :seqno seqno :utime utime :lt end-lt
                                     :accounts-root accounts-root
                                     :total (%safe-total fc)
                                     :master-ref nil))
         (prev-sh-ref (if prev
                          (%ext-ref (fc-block-end-lt prev) (fc-block-seqno prev)
                                    (fc-block-sh-root prev) (fc-block-sh-file prev))
                          (%ext-ref 0 0 (fakechain-wc0-zero-root fc) (fakechain-wc0-zero-file fc))))
         (prev-mc-ref (if prev
                          (%ext-ref (fc-block-end-lt prev) (fc-block-seqno prev)
                                    (fc-block-mc-root prev) (fc-block-mc-file prev))
                          (%ext-ref 0 0 (fakechain-zero-root fc) (fakechain-zero-file fc))))
         (sh-info (%block-info-cell :not-master t :seqno seqno :workchain 0 :shard +mc-shard+
                                    :utime utime :start-lt start-lt :end-lt end-lt
                                    :prev-ref prev-sh-ref :master-ref prev-mc-ref))
         (sh-block (build-block :info sh-info :utime utime
                                :state-update (make-state-update old-wc0 new-wc0)))
         (sh-root (node-hash sh-block))
         (sh-file (%file-hash sh-block))
         (leaf (%shard-leaf-for :seqno seqno :reg-mc seqno :start-lt start-lt :end-lt end-lt
                                :root sh-root :file sh-file :utime utime))
         (old-mc (if prev (fc-block-mc-state prev) (fakechain-zero-state fc)))
         (new-mc (%mc-state fc :seqno seqno :utime utime :lt end-lt :wc0-leaf leaf))
         (mc-info (%block-info-cell :not-master nil :seqno seqno :workchain -1 :shard +mc-shard+
                                    :utime utime :start-lt start-lt :end-lt end-lt
                                    :prev-ref prev-mc-ref))
         (mc-block (build-block :info mc-info :utime utime
                                :state-update (make-state-update old-mc new-mc)))
         (mc-root (node-hash mc-block))
         (mc-file (%file-hash mc-block))
         (sig (sign-octets (fakechain-validator fc)
                           (tl-encode (tl-make "ton.blockId" :root-cell-hash mc-root :file-hash mc-file))))
         (blk (make-fc-block :seqno seqno :utime utime :start-lt start-lt :end-lt end-lt
                             :mc-block mc-block :mc-state new-mc :mc-root mc-root :mc-file mc-file
                             :sh-block sh-block :sh-state new-wc0 :sh-root sh-root :sh-file sh-file
                             :signature sig
                             :accounts (fc-snapshot-accounts fc))))
    (setf (fakechain-lt fc) end-lt)
    (dolist (p processed)
      (push (cons (car p) blk) (gethash (fc-address-key (cdr p)) (fakechain-txs fc))))
    (vector-push-extend blk (fakechain-blocks fc))
    blk))

(defun fc-snapshot-accounts (fc)
  (let ((h (make-hash-table)))
    (maphash (lambda (k v) (setf (gethash k h) v)) (fakechain-accounts fc))
    h))

(defun %safe-total (fc)
  (loop for sa being the hash-values of (fakechain-accounts fc) sum (%safe-balance sa)))

(defun fakechain-tick (fc)
  "Advance the virtual clock one block: emulate the queued messages, seal a
masterchain + workchain-0 block pair.  Returns the new FC-BLOCK."
  (with-fc-lock (fc)
    (unless (fakechain-stall-p fc)
      (fc-seal-block fc (fc-tick-messages fc)))))

;;; ---------------------------------------------------------------------------
;;; liteServer.* answers
;;; ---------------------------------------------------------------------------

(defun fc-mc-id (blk)
  (tl-block-id-ext :workchain -1 :shard (- (expt 2 63)) :seqno (fc-block-seqno blk)
                   :root-hash (fc-block-mc-root blk) :file-hash (fc-block-mc-file blk)))

(defun fc-sh-id (blk)
  (tl-block-id-ext :workchain 0 :shard (- (expt 2 63)) :seqno (fc-block-seqno blk)
                   :root-hash (fc-block-sh-root blk) :file-hash (fc-block-sh-file blk)))

(defun fc-zero-id (fc)
  (tl-block-id-ext :workchain -1 :shard (- (expt 2 63)) :seqno 0
                   :root-hash (fakechain-zero-root fc) :file-hash (fakechain-zero-file fc)))

(defun fc-zero-state-id (fc)
  (tl-make "tonNode.zeroStateIdExt" :workchain -1
           :root-hash (fakechain-zero-root fc) :file-hash (fakechain-zero-file fc)))

(defun fc-error (code message)
  (tl-encode (tl-make "liteServer.error" :code code :message message)))

(defun fc-find-block (fc seqno)
  (let ((blocks (fakechain-blocks fc)))
    (find seqno blocks :key #'fc-block-seqno)))

(defun fc-proof-boc (&rest nodes)
  (serialize-boc (mapcar #'make-merkle-proof nodes) :has-crc32c nil))

(defun fc-cells-boc (cells)
  (if cells (serialize-boc cells :has-crc32c nil) (make-array 0 :element-type '(unsigned-byte 8))))

(defun fc-validator-set-hash () +fc-validator-set-hash+)

(defun fc-forward-link (fc from-id blk)
  (tl-make "liteServer.blockLinkForward"
           :to-key-block nil :from from-id :to (fc-mc-id blk)
           :dest-proof (fc-proof-boc (fc-block-mc-block blk))
           :config-proof (fc-proof-boc (fakechain-zero-state fc))
           :signatures (tl-make "liteServer.signatureSet"
                                :validator-set-hash (fc-validator-set-hash) :catchain-seqno 0
                                :signatures (vector (tl-make "liteServer.signature"
                                                             :node-id-short (adnl-short-id (keypair-public (fakechain-validator fc)))
                                                             :signature (fc-block-signature blk))))))

(defun fc-answer-masterchain-info (fc)
  (let ((h (fc-head fc)))
    (tl-encode (tl-make "liteServer.masterchainInfo" :last (fc-mc-id h)
                                                    :state-root-hash (node-hash (fc-block-mc-state h))
                                                    :init (fc-zero-state-id fc)))))

(defun fc-answer-masterchain-info-ext (fc)
  (let ((h (fc-head fc)))
    (tl-encode (tl-make "liteServer.masterchainInfoExt" :mode 0 :version 2 :capabilities 7
                                                       :last (fc-mc-id h) :last-utime (fc-block-utime h)
                                                       :now (fc-now fc)
                                                       :state-root-hash (node-hash (fc-block-mc-state h))
                                                       :init (fc-zero-state-id fc)))))

(defun fc-answer-block-proof (fc fn)
  (let* ((known (tl-get fn :known-block))
         (mode (tl-get fn :mode))
         (target-seqno (if (logbitp 0 mode)
                           (tl-get (tl-get fn :target-block) :seqno)
                           (fc-head-seqno fc)))
         (blk (fc-find-block fc target-seqno)))
    (cond
      ((null blk) (fc-error 651 "target block not found"))
      ((= (tl-get known :seqno) target-seqno)
       (tl-encode (tl-make "liteServer.partialBlockProof" :complete t :from known :to (fc-mc-id blk)
                                                         :steps (vector))))
      ((zerop (tl-get known :seqno))
       (tl-encode (tl-make "liteServer.partialBlockProof" :complete t :from known :to (fc-mc-id blk)
                                                         :steps (vector (fc-forward-link fc known blk)))))
      (t (fc-error 651 "unsupported block proof request")))))

(defun fc-account-from-blk (blk addr-obj)
  (let ((accounts (fc-block-accounts blk))
        (key (octets->uint (tl-get addr-obj :id))))
    (values (and (eql (tl-get addr-obj :workchain) 0) (gethash key accounts)) key)))

(defun fc-account-cell (shard-account)
  "The ^Account of a ShardAccount, or NIL for account_none."
  (let ((acc (first-ref-cell shard-account)))
    (and (plusp (cell-bit-length acc)) (= 1 (cell-uint acc 0 1)) acc)))

(defun fc-answer-account-state (fc fn)
  (let* ((id (tl-get fn :id))
         (blk (or (fc-find-block fc (tl-get id :seqno)) (fc-head fc)))
         (addr (tl-get fn :account)))
    (multiple-value-bind (sa) (fc-account-from-blk blk addr)
      (let ((acc (and sa (fc-account-cell sa))))
        (tl-encode
         (tl-make "liteServer.accountState"
                  :id (fc-mc-id blk) :shardblk (fc-sh-id blk)
                  :shard-proof (fc-proof-boc (fc-block-mc-block blk) (fc-block-mc-state blk))
                  :proof (fc-proof-boc (fc-block-sh-block blk) (fc-block-sh-state blk))
                  :state (if acc (fc-cells-boc (list acc)) (fc-cells-boc '()))))))))

(defun fc-tx-lt (tx)
  (cell-uint tx (+ 4 256) 64))

(defun fc-answer-transactions (fc fn)
  (let* ((addr (tl-get fn :account))
         (key (octets->uint (tl-get addr :id)))
         (all (gethash key (fakechain-txs fc)))
         (start (position-if (lambda (e) (and (= (fc-tx-lt (car e)) (tl-get fn :lt))
                                              (equalp (node-hash (car e)) (tl-get fn :hash))))
                             all))
         (picked (if start (subseq all start (min (length all) (+ start (tl-get fn :count)))) '())))
    (if (null picked)
        (fc-error 651 "cannot find transaction")
        (tl-encode (tl-make "liteServer.transactionList"
                            :ids (map 'vector (lambda (e) (fc-sh-id (cdr e))) picked)
                            :transactions (fc-cells-boc (mapcar #'car picked)))))))

(defun fc-answer-list-block-transactions (fc fn)
  "liteServer.listBlockTransactions served from the chain model (no proof: tonlib
only asks for one with want_proof).  Order is (account, lt) ascending, or descending
with reverse_order; AFTER (a transactionId3) is exclusive; the answer is INCOMPLETE
when more transactions remain than COUNT."
  (let* ((id (tl-get fn :id))
         (mode (tl-get fn :mode))
         (blk (and (= (tl-get id :workchain) 0) (fc-find-block fc (tl-get id :seqno))))
         (after (tl-get fn :after))
         (reverse (tl-get fn :reverse-order))
         (count (min (tl-get fn :count) 1000))
         (entries '()))
    (when (and blk (equalp (tl-get id :root-hash) (fc-block-sh-root blk)))
      (maphash (lambda (key list)
                 (dolist (e list)
                   (when (eq (cdr e) blk)
                     (push (list key (fc-tx-lt (car e)) (car e)) entries))))
               (fakechain-txs fc)))
    (setf entries (sort entries (lambda (a b) (or (< (first a) (first b))
                                                  (and (= (first a) (first b)) (< (second a) (second b)))))))
    (when reverse (setf entries (nreverse entries)))
    (when after
      (let ((ak (octets->uint (tl-get after :account))) (al (tl-get after :lt)))
        (setf entries (remove-if-not (lambda (e)
                                       (if reverse
                                           (or (< (first e) ak) (and (= (first e) ak) (< (second e) al)))
                                           (or (> (first e) ak) (and (= (first e) ak) (> (second e) al)))))
                                     entries))))
    (let* ((page (subseq entries 0 (min count (length entries))))
           (incomplete (> (length entries) (length page))))
      (tl-encode
       (tl-make "liteServer.blockTransactions"
                :id id :req-count count :incomplete incomplete
                :ids (map 'vector
                          (lambda (e)
                            (tl-make "liteServer.transactionId" :mode (logand mode 7)
                                     :account (uint->octets (first e) 32)
                                     :lt (second e) :hash (node-hash (third e))))
                          page)
                :proof (make-array 0 :element-type '(unsigned-byte 8)))))))

(defun fc-answer-send-message (fc fn)
  (let* ((body (tl-get fn :body))
         (msg (handler-case (parse-boc body) (error () nil))))
    (cond
      ((null msg) (fc-error 400 "cannot parse message BOC"))
      (t (with-fc-lock (fc)
           (if (plusp (fakechain-drop-externals fc))
               (decf (fakechain-drop-externals fc))
               (setf (fakechain-queue fc) (append (fakechain-queue fc) (list (if (listp msg) (first msg) msg)))))
           (push (list :send (get-universal-time)) (fakechain-log fc)))
         (tl-encode (tl-make "liteServer.sendMsgStatus" :status 1))))))

(defun fc-answer-config-all (fc fn)
  (declare (ignore fn))
  (let ((h (fc-head fc)))
    (tl-encode (tl-make "liteServer.configInfo" :mode 0 :id (fc-mc-id h)
                                               :state-proof (fc-proof-boc (fc-block-mc-block h))
                                               :config-proof (fc-proof-boc (fc-block-mc-state h))))))

(defun fc-answer-block-header (fc fn)
  (let* ((id (tl-get fn :id))
         (blk (fc-find-block fc (tl-get id :seqno))))
    (if blk
        (tl-encode (tl-make "liteServer.blockHeader" :id (fc-mc-id blk) :mode 0
                                                     :header-proof (fc-proof-boc (fc-block-mc-block blk))))
        (fc-error 651 "block not found"))))

(defun fc-wait-for-seqno (fc seqno timeout-ms)
  "Block until the head reaches SEQNO; NIL on timeout."
  (loop with deadline = (+ (get-internal-real-time) (* timeout-ms (/ internal-time-units-per-second 1000)))
        do (when (>= (fc-head-seqno fc) seqno) (return t))
           (when (or (>= (get-internal-real-time) deadline) (fakechain-stopped fc)) (return nil))
           (sleep 0.02)))

(defun fakechain-handle-query (fc server conn query-id query)
  (declare (ignore server conn query-id))
  (let ((outer (handler-case (tl-decode query) (error () nil))))
    (unless (tl-is outer "liteServer.query") (return-from fakechain-handle-query (fc-error 400 "expected liteServer.query")))
    (when (plusp (fakechain-answer-delay fc)) (sleep (fakechain-answer-delay fc)))
    (when (with-fc-lock (fc) (and (plusp (fakechain-fail-next fc)) (decf (fakechain-fail-next fc))))
      (return-from fakechain-handle-query (fc-error 502 "injected failure")))
    (multiple-value-bind (wait rest) (proxy-split-query (tl-get outer :data))
      (when wait                        ; record what a proxy forwarded (watermark tests)
        (with-fc-lock (fc)
          (push (list :wait (tl-get wait :seqno) (tl-get wait :timeout-ms)) (fakechain-log fc))))
      (when (and wait (not (fc-wait-for-seqno fc (tl-get wait :seqno) (tl-get wait :timeout-ms))))
        (return-from fakechain-handle-query (fc-error 652 "timeout")))
      (let ((fn (handler-case (tl-decode rest) (error () nil))))
        (with-fc-lock (fc)
          (push (list :query (if (tl-obj-p fn) (tl-obj-name fn) :unknown)) (fakechain-log fc))
          (let ((custom (loop for h in (fakechain-extra-handlers fc)
                              for r = (funcall h fc fn) when r return r)))
            (or custom
                (cond
                  ((not (tl-obj-p fn))
                   (fc-error 400 (format nil "unknown query ~A"
                                         (if (consp fn)
                                             (format nil "constructor ~8,'0X, ~D argument octets" (car fn)
                                                     (length (cdr fn)))
                                             "(undecodable)"))))
                  ((and (fakechain-lagging-p fc) (not (tl-is fn "liteServer.getMasterchainInfo")))
                   (push (list :lagging) (fakechain-log fc))
                   (fc-error 651 "cannot load block (0,8000000000000000,101118425):036820895A902C35FE9B4301446F7363CA65498862FDA53397589226D6D8C010:355C342C61164E84EC168965DAA6956FF5D69FF019F0816E610583ACA1DF4550 : block (0,8000000000000000,101118425) is not in db (possibly out of sync: shard_client_seqno=96600614 ls_seqno=96601319)"))
                  ((tl-is fn "liteServer.getMasterchainInfo") (fc-answer-masterchain-info fc))
                  ((tl-is fn "liteServer.getMasterchainInfoExt") (fc-answer-masterchain-info-ext fc))
                  ((tl-is fn "liteServer.getTime")
                   (tl-encode (tl-make "liteServer.currentTime" :now (fc-now fc))))
                  ((tl-is fn "liteServer.getVersion")
                   (tl-encode (tl-make "liteServer.version" :mode 0 :version #x101 :capabilities 7 :now (fc-now fc))))
                  ((tl-is fn "liteServer.getBlockProof") (fc-answer-block-proof fc fn))
                  ((tl-is fn "liteServer.getAccountState") (fc-answer-account-state fc fn))
                  ((tl-is fn "liteServer.getTransactions") (fc-answer-transactions fc fn))
                  ((tl-is fn "liteServer.listBlockTransactions") (fc-answer-list-block-transactions fc fn))
                  ((tl-is fn "liteServer.sendMessage") (fc-answer-send-message fc fn))
                  ((tl-is fn "liteServer.getConfigAll") (fc-answer-config-all fc fn))
                  ((tl-is fn "liteServer.getLibraries") (fc-answer-get-libraries fc fn))
                  ((tl-is fn "liteServer.getBlockHeader") (fc-answer-block-header fc fn))
                  (t (fc-error 651 (format nil "fakechain: ~A not supported" (tl-obj-name fn))))))))))))

;;; --- lifecycle ---------------------------------------------------------------------

(defun start-fakechain (&key (port 0) (host "127.0.0.1") (time-mode :manual) (tick-seconds 3)
                          (tick-interval 1) fc)
  "Create (or take FC) and listen.  TIME-MODE :MANUAL (blocks only via
FAKECHAIN-TICK / FAKECHAIN-ADVANCE) or :REALTIME (a ticker thread seals a block
every TICK-INTERVAL seconds of wall time)."
  (let ((fc (or fc (make-fakechain :time-mode time-mode :tick-seconds tick-seconds
                                   :tick-interval tick-interval))))
    (setf (fakechain-server fc)
          (start-adnl-ext-server :keypair (fakechain-keypair fc) :host host :port port
                                 :handler (lambda (server conn query-id query)
                                            (fakechain-handle-query fc server conn query-id query))))
    (when (eq (fakechain-time-mode fc) :realtime)
      (setf (fakechain-ticker fc)
            (sb-thread:make-thread
             (lambda ()
               (loop until (fakechain-stopped fc)
                     do (sleep (fakechain-tick-interval fc))
                        (ignore-errors (fakechain-tick fc))))
             :name "fakechain ticker")))
    fc))

(defun stop-fakechain (fc)
  (when fc
    (setf (fakechain-stopped fc) t)
    (when (fakechain-server fc) (stop-adnl-ext-server (fakechain-server fc)))
    (let ((th (fakechain-ticker fc)))
      (when (and th (not (eq th sb-thread:*current-thread*)))
        (sb-thread:join-thread th :default nil :timeout 3))))
  nil)

(defun fakechain-port (fc) (adnl-ext-server-port (fakechain-server fc)))

(defun fakechain-advance (fc &optional (blocks 1))
  (dotimes (i blocks) (fakechain-tick fc))
  (fc-head-seqno fc))

(defun fakechain-liteserver-entry (fc)
  "The liteservers entry (a JSON-ready plist string) for this chain."
  (format nil "{\"ip\":2130706433,\"port\":~D,\"id\":{\"@type\":\"pub.ed25519\",\"key\":\"~A\"}}"
          (fakechain-port fc) (base64-encode (keypair-public (fakechain-keypair fc)))))

(defun fakechain-write-global-config (fc path)
  "Write a global config whose ONLY liteserver is this chain, with the chain's
zero state as validator.zero_state.  Returns PATH."
  (ensure-directories-exist path)
  (with-open-file (o path :direction :output :if-exists :supersede)
    (format o "{\"@type\":\"config.global\",\"liteservers\":[~A],\"dht\":{\"@type\":\"dht.config.global\",\"k\":6,\"a\":3,\"static_nodes\":{\"@type\":\"dht.nodes\",\"nodes\":[]}},\"validator\":{\"@type\":\"validator.config.global\",\"zero_state\":{\"workchain\":-1,\"shard\":-9223372036854775808,\"seqno\":0,\"root_hash\":\"~A\",\"file_hash\":\"~A\"}}}"
            (fakechain-liteserver-entry fc)
            (base64-encode (fakechain-zero-root fc)) (base64-encode (fakechain-zero-file fc))))
  path)


;;; ---------------------------------------------------------------------------
;;; Account fixtures: capture a real contract once, replay it in the fakechain
;;; ---------------------------------------------------------------------------
;;;
;;; A fixture is a small JSON file {address, balance, code, data} with code and
;;; data as base64 BOCs.  WRITE-ACCOUNT-FIXTURE takes the ACCOUNT-STATE any
;;; tonlib returned (so it works against mainnet, testnet or another fakechain);
;;; FAKECHAIN-LOAD-FIXTURE seeds the fakechain with that contract.  This is how
;;; DEX pool/router/vault/jetton-wallet state gets into the test network: capture
;;; each contract once with network access, commit the files, replay offline.

(defun write-account-fixture (state path &key libraries)
  "Write the ACCOUNT-STATE STATE (an ACTIVE account) to PATH as a fixture; returns PATH.
LIBRARIES (alist hash-hex . cell, as TONLIB-LIBRARIES returns) are stored with it: the
library cells the account's code/data reference."
  (unless (and (eq (account-state-status state) :active)
               (account-state-code state) (account-state-data state))
    (ton-error "cannot capture ~A: account is not active with code and data"
               (address->string (account-state-address state))))
  (ensure-directories-exist path)
  (with-open-file (o path :direction :output :if-exists :supersede)
    (format o "{\"address\":\"~A\",\"balance\":~D,\"code\":\"~A\",\"data\":\"~A\",\"libraries\":[~{\"~A\"~^,~}]}~%"
            (address->string (account-state-address state) :bounceable t :url nil)
            (account-state-balance state)
            (cell->base64 (account-state-code state))
            (cell->base64 (account-state-data state))
            (mapcar (lambda (entry) (cell->base64 (cdr entry))) libraries)))
  path)

(defun read-account-fixture (path)
  "Returns (VALUES ADDRESS CODE-CELL DATA-CELL BALANCE) from a fixture file."
  (let ((j (json-decode (uiop:read-file-string path))))
    (values (parse-address (json-get j "address"))
            (base64->cell (json-get j "code"))
            (base64->cell (json-get j "data"))
            (json-get j "balance"))))

(defun fakechain-load-fixture (fc path &key balance)
  "Seed FC with the contract captured at PATH, at its original address, with its
captured balance (or BALANCE).  Returns the address."
  (multiple-value-bind (addr code data captured-balance) (read-account-fixture path)
    (fakechain-set-account fc addr :code code :data data :balance (or balance captured-balance))
    ;; the library cells the fixture was captured with
    (dolist (b64 (json-get (json-decode (uiop:read-file-string path)) "libraries"))
      (fakechain-add-library fc (base64->cell b64)))
    addr))
