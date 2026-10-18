;;;; verify.lisp -- tests for proof-verify.lisp: what a liteserver says is believed only after the
;;;; proofs lead from a trusted block hash to the answer.
;;;;
;;;; The answers come from the fakechain, whose proofs the real tonlibjson.so accepts (see
;;;; cells.lisp).  Every way an answer can be wrong gets its own test, and each must be refused with
;;;; a PROOF-ERROR -- not with whatever incidental error the bad data happened to trip.

(in-package :cl-ton/test)

(defvar *verify-state* (sb-ext:seed-random-state 20261010))
(defun %vrnd (n) (random n *verify-state*))

(defun test-dict-lookup ()
  (format t "verify: dictionary lookup~%")
  (let ((wrong 0) (total 0))
    (dolist (key-bits '(8 16 64 256))
      (dotimes (round 40)
        (let* ((count (1+ (%vrnd 12)))
               (table (make-hash-table))
               (entries '()))
          (dotimes (i count)
            (let ((key (%vrnd (ash 1 key-bits))) (value (%vrnd (ash 1 32))))
              (unless (gethash key table)
                (setf (gethash key table) value)
                (push (cons key (let ((v value)) (lambda (b) (cl-ton:store-uint b v 32)))) entries))))
          (let ((root (cl-ton::hashmap-cell entries key-bits)))
            (loop for key being the hash-keys of table using (hash-value value)
                  do (incf total)
                     (multiple-value-bind (slice found) (cl-ton:dict-lookup root key key-bits)
                       (unless (and found (= value (cl-ton:load-uint slice 32))) (incf wrong))))
            (dotimes (i 20)
              (let ((key (%vrnd (ash 1 key-bits))))
                (unless (gethash key table)
                  (incf total)
                  (when (nth-value 1 (cl-ton:dict-lookup root key key-bits)) (incf wrong)))))))))
    (check (format nil "~D lookups of present and absent keys in random dictionaries (8, 16, 64, 256-bit keys) agree with a hash table" total)
           (zerop wrong)))
  (check "an empty dictionary finds nothing" (not (nth-value 1 (cl-ton:dict-lookup nil 5 8)))))

(defun %answer-with (answer &rest changes)
  "A copy of the liteServer.accountState ANSWER with some fields replaced."
  (let ((fields (copy-list (cl-ton::tl-obj-fields answer))))
    (loop for (k v) on changes by #'cddr do (setf (getf fields k) v))
    (apply #'cl-ton::tl-make "liteServer.accountState" fields)))

(defun %id-with (id &rest changes)
  (let ((fields (copy-list (cl-ton::tl-obj-fields id))))
    (loop for (k v) on changes by #'cddr do (setf (getf fields k) v))
    (apply #'cl-ton::tl-make (cl-ton::tl-obj-name id) fields)))

(defun %flip-octet (octets index &optional (mask 1))
  (let ((v (copy-seq octets))) (setf (aref v index) (logxor (aref v index) mask)) v))

(defun %served-answer (fc blk addr)
  (cl-ton::tl-decode
   (cl-ton::fc-answer-account-state
    fc (cl-ton::tl-make "liteServer.getAccountState" :id (cl-ton::fc-mc-id blk)
                        :account (cl-ton::tl-make "liteServer.accountId" :workchain 0
                                                  :id (cl-ton:address-hash addr))))))

(defun %forge-pruned (root)
  "ROOT's tree rebuilt bottom-up with the first pruned branch's stored hash changed: an attacker's
consistent forgery (every ancestor, every Merkle proof cell recomputed)."
  (let ((done nil))
    (labels ((rebuild (node)
               (cond ((not (cl-ton:cell-p node)) node)
                     ((and (not done) (cl-ton:pruned-branch-p node))
                      (setf done t)
                      (cl-ton:make-cell :exotic t :bit-length (cl-ton:cell-bit-length node)
                                        :bits (logxor (cl-ton:cell-bits node) (ash 1 (+ 16 (* 16 1))))
                                        :refs '()))
                     ((= 3 (cl-ton:cell-special-type node))
                      (cl-ton::make-merkle-proof (rebuild (svref (cl-ton:cell-refs node) 0))))
                     (t (cl-ton:make-cell :bits (cl-ton:cell-bits node) :bit-length (cl-ton:cell-bit-length node)
                                          :exotic (cl-ton:cell-exotic-p node)
                                          :refs (map 'list #'rebuild (cl-ton:cell-refs node)))))))
      (values (rebuild root) done))))

(defun test-verify-account-state ()
  (format t "verify: an account-state answer, from a trusted block hash down~%")
  (if (not (%libs-available-p))
      (skip-missing "account-state verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (cl-ton:wallet-address w))
                (other (fake-address #x66))
                (absent (fake-address #x77)))
           (cl-ton::fakechain-set-account fc other :balance (cl-ton::nano 1))
           (cl-ton::fakechain-advance fc 2)
           (let* ((blk (cl-ton::fc-head fc))
                  (trusted (cl-ton::fc-mc-id blk))
                  (answer (%served-answer fc blk addr))
                  (absent-answer (%served-answer fc blk absent))
                  (result (cl-ton:verify-account-state answer addr trusted)))
             (check "a genuine answer verifies: the account exists, its cell is the served state"
                    (and (getf result :exists)
                         (equalp (cl-ton:node-hash (getf result :account-cell))
                                 (cl-ton:node-hash (first (cl-ton:parse-boc (cl-ton::tl-get answer :state)))))
                         (integerp (getf result :last-trans-lt))
                         (= 32 (length (getf result :last-trans-hash)))))
             (check "...and the shard block it was proved in is the one named"
                    (equalp (cl-ton::tl-get (getf result :shard-block) :root-hash)
                            (cl-ton::tl-get (cl-ton::tl-get answer :shardblk) :root-hash)))
             (check "an account the proof shows absent verifies as absent, with no state"
                    (let ((r (cl-ton:verify-account-state absent-answer absent trusted)))
                      (and (not (getf r :exists)) (zerop (length (cl-ton::tl-get absent-answer :state))))))
             (macrolet ((refuses (what form)
                          `(check ,what (%signals cl-ton:proof-error ,form))))
               ;; -- the trusted block
               (refuses "a different trusted root hash (the answer is about some other block)"
                        (cl-ton:verify-account-state
                         answer addr (%id-with trusted :root-hash (%flip-octet (cl-ton::tl-get trusted :root-hash) 0))))
               (refuses "a different trusted seqno"
                        (cl-ton:verify-account-state
                         answer addr (%id-with trusted :seqno (1+ (cl-ton::tl-get trusted :seqno)))))
               (refuses "an answer claiming another masterchain block than it proves"
                        (cl-ton:verify-account-state
                         (%answer-with answer :id (%id-with (cl-ton::tl-get answer :id)
                                                            :root-hash (%flip-octet (cl-ton::tl-get trusted :root-hash) 3)))
                         addr trusted))
               ;; -- the shard block the masterchain is said to place the account in
               (let ((sb (cl-ton::tl-get answer :shardblk)))
                 (refuses "a shard block with the wrong seqno"
                          (cl-ton:verify-account-state
                           (%answer-with answer :shardblk (%id-with sb :seqno (1+ (cl-ton::tl-get sb :seqno)))) addr trusted))
                 (refuses "a shard block with the wrong root hash"
                          (cl-ton:verify-account-state
                           (%answer-with answer :shardblk (%id-with sb :root-hash (%flip-octet (cl-ton::tl-get sb :root-hash) 0)))
                           addr trusted))
                 (refuses "a shard block with the wrong file hash"
                          (cl-ton:verify-account-state
                           (%answer-with answer :shardblk (%id-with sb :file-hash (%flip-octet (cl-ton::tl-get sb :file-hash) 0)))
                           addr trusted))
                 (refuses "a shard block of another shard"
                          (cl-ton:verify-account-state
                           (%answer-with answer :shardblk (%id-with sb :shard (- (cl-ton::tl-get sb :shard) 1))) addr trusted))
                 (refuses "a shard block of another workchain"
                          (cl-ton:verify-account-state
                           (%answer-with answer :shardblk (%id-with sb :workchain -1)) addr trusted)))
               ;; -- the proofs
               (refuses "the two proof BOCs swapped"
                        (cl-ton:verify-account-state
                         (%answer-with answer :shard-proof (cl-ton::tl-get answer :proof)
                                              :proof (cl-ton::tl-get answer :shard-proof))
                         addr trusted))
               (refuses "an empty shard proof, an empty account proof"
                        (cl-ton:verify-account-state (%answer-with answer :shard-proof (make-array 0 :element-type '(unsigned-byte 8))) addr trusted))
               (refuses "garbage instead of the account proof"
                        (cl-ton:verify-account-state
                         (%answer-with answer :proof (coerce (loop repeat 60 collect (%vrnd 256)) '(vector (unsigned-byte 8)))) addr trusted))
               (refuses "a truncated account proof"
                        (cl-ton:verify-account-state
                         (%answer-with answer :proof (subseq (cl-ton::tl-get answer :proof) 0
                                                             (floor (length (cl-ton::tl-get answer :proof)) 2)))
                         addr trusted))
               (refuses "a single flipped byte in the account proof (the BOC checksum is not the defence)"
                        (let ((p (cl-ton::tl-get answer :proof)))
                          (cl-ton:verify-account-state
                           (%answer-with answer :proof (%flip-octet p (floor (length p) 2))) addr trusted)))
               (refuses "the shard proof of a different masterchain block"
                        (progn
                          (cl-ton::fakechain-advance fc 3)
                          (let ((newer (%served-answer fc (cl-ton::fc-head fc) addr)))
                            (cl-ton:verify-account-state (%answer-with answer :shard-proof (cl-ton::tl-get newer :shard-proof))
                                                         addr trusted))))
               ;; -- a forgery an attacker could build consistently
               (let* ((roots (cl-ton:parse-boc (cl-ton::tl-get answer :proof)))
                      (forged-state (%forge-pruned (second roots))))
                 (check "(the forgery below really changes a pruned branch)" (nth-value 1 (%forge-pruned (second roots))))
                 (refuses "an account proof BOC holding only the block proof (two roots are needed)"
                          (cl-ton:verify-account-state
                           (%answer-with answer :proof (cl-ton:serialize-boc (first roots))) addr trusted))
                 (refuses "a consistently rebuilt state proof (every ancestor recomputed) with one pruned branch's hash changed"
                          (cl-ton:verify-account-state
                           (%answer-with answer :proof (cl-ton::fc-proof-boc (first roots) forged-state)) addr trusted)))
               ;; -- the served state
               (refuses "a served state with one byte changed"
                        (cl-ton:verify-account-state
                         (%answer-with answer :state (%flip-octet (cl-ton::tl-get answer :state)
                                                                  (floor (length (cl-ton::tl-get answer :state)) 2)))
                         addr trusted))
               (refuses "no state for an account the proof shows present"
                        (cl-ton:verify-account-state
                         (%answer-with answer :state (make-array 0 :element-type '(unsigned-byte 8))) addr trusted))
               (refuses "a state served for an account the proof shows absent"
                        (cl-ton:verify-account-state
                         (%answer-with absent-answer :state (cl-ton::tl-get answer :state)) absent trusted))
               ;; -- the wrong account
               (refuses "the answer for one account offered as the answer for another"
                        (cl-ton:verify-account-state answer other trusted))
               (refuses "the answer about one account offered for an absent one (it would claim a state)"
                        (cl-ton:verify-account-state answer absent trusted)))))))))

(defun test-verify-fuzz ()
  (format t "verify: corrupted answers are only ever refused with a proof-error~%")
  (if (not (%libs-available-p))
      (skip-missing "verification fuzz (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((w (%seed-wallet fc)) (addr (cl-ton:wallet-address w)))
           (cl-ton::fakechain-advance fc 2)
           (let* ((blk (cl-ton::fc-head fc)) (trusted (cl-ton::fc-mc-id blk))
                  (answer (%served-answer fc blk addr))
                  (accepted 0) (refused 0) (other '()))
             (flet ((try (altered)
                      (handler-case (progn (cl-ton:verify-account-state altered addr trusted) (incf accepted))
                        (cl-ton:proof-error () (incf refused))
                        (error (e) (push (princ-to-string e) other)))))
               (dolist (field '(:proof :shard-proof :state))
                 (let ((octets (cl-ton::tl-get answer field)))
                   (dotimes (i 150)
                     (let ((v (copy-seq octets)))
                       (dotimes (k (1+ (%vrnd 3)))
                         (setf (aref v (%vrnd (length v))) (%vrnd 256)))
                       (try (%answer-with answer field v))))
                   (dotimes (i 25)               ; truncations and garbage tails
                     (try (%answer-with answer field (subseq octets 0 (%vrnd (length octets)))))
                     (try (%answer-with answer field (concatenate '(vector (unsigned-byte 8)) octets
                                                                  (loop repeat (1+ (%vrnd 9)) collect (%vrnd 256))))))))
               (check (format nil "600 randomly corrupted answers (byte changes, truncations, garbage tails): ~D refused, ~D happened to still verify, ~D failed with another kind of error ~S"
                              refused accepted (length other) (subseq other 0 (min 3 (length other))))
                      (null other))
               (check "...and nothing corrupted verifies unless it left the proofs and state intact"
                      (< accepted 5)))))))))

;;; --- transaction lists ---------------------------------------------------------------

(defun %tx-answer (fc addr lt hash count)
  (cl-ton::tl-decode
   (cl-ton::fc-answer-transactions
    fc (cl-ton::tl-make "liteServer.getTransactions" :count count
                        :account (cl-ton::tl-make "liteServer.accountId" :workchain 0
                                                  :id (cl-ton:address-hash addr))
                        :lt lt :hash hash))))

(defun %tx-list-with (answer &key (roots nil roots-p) (ids nil ids-p))
  "A liteServer.transactionList like ANSWER with the transaction roots and/or block ids replaced."
  (cl-ton::tl-make "liteServer.transactionList"
                   :ids (if ids-p ids (cl-ton::tl-get answer :ids))
                   :transactions (if roots-p
                                     (if roots (cl-ton::fc-cells-boc roots)
                                         (make-array 0 :element-type '(unsigned-byte 8)))
                                     (cl-ton::tl-get answer :transactions))))

(defun test-verify-transactions ()
  (format t "verify: a transaction list, from the account's last transaction down~%")
  (if (not (%libs-available-p))
      (skip-missing "transaction-list verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (cl-ton:wallet-address w))
                (dest (fake-address #x66))
                (other (fake-address #x77)))
           (cl-ton::fakechain-set-account fc other :balance (cl-ton::nano 1))
           (dotimes (seqno 4)
             (%fc-enqueue fc (%transfer w seqno dest (cl-ton::nano 1/10)))
             (cl-ton::fakechain-advance fc 2))
           (let* ((blk (cl-ton::fc-head fc))
                  (trusted (cl-ton::fc-mc-id blk))
                  (state (cl-ton:verify-account-state (%served-answer fc blk addr) addr trusted))
                  (lt (getf state :last-trans-lt))
                  (hash (getf state :last-trans-hash))
                  (answer (%tx-answer fc addr lt hash 20))
                  (result (cl-ton:verify-transaction-list answer addr lt hash :count 20))
                  (txs (getf result :transactions))
                  (roots (cl-ton:parse-boc (cl-ton::tl-get answer :transactions))))
             (check "the wallet has its four transactions, newest first, from the verified last transaction"
                    (and (= 4 (length txs)) (= lt (getf (first txs) :lt))
                         (apply #'> (mapcar (lambda (e) (getf e :lt)) txs))))
             (check "...and the list ends at the account's first transaction"
                    (and (getf result :complete) (zerop (getf result :next-lt))))
             (check "a short page continues where it stopped, and the pages add up to the whole list"
                    (let* ((p1-answer (%tx-answer fc addr lt hash 3))
                           (p1 (cl-ton:verify-transaction-list p1-answer addr lt hash :count 3))
                           (p2 (cl-ton:verify-transaction-list
                                (%tx-answer fc addr (getf p1 :next-lt) (getf p1 :next-hash) 3)
                                addr (getf p1 :next-lt) (getf p1 :next-hash) :count 3)))
                      (and (not (getf p1 :complete)) (= 3 (length (getf p1 :transactions)))
                           (getf p2 :complete)
                           (equalp (mapcar (lambda (e) (getf e :hash)) txs)
                                   (mapcar (lambda (e) (getf e :hash))
                                           (append (getf p1 :transactions) (getf p2 :transactions)))))))
             (macrolet ((refuses (what form)
                          `(check ,what (%signals cl-ton:proof-error ,form))))
               (refuses "a start hash that is not the newest transaction's"
                        (cl-ton:verify-transaction-list answer addr lt (%flip-octet hash 0)))
               (refuses "a start lt that is not the newest transaction's"
                        (cl-ton:verify-transaction-list answer addr (1+ lt) hash))
               (refuses "a start that is an older transaction than the first one served"
                        (cl-ton:verify-transaction-list answer addr (getf (second txs) :lt) (getf (second txs) :hash)))
               (refuses "no start at all (lt 0)"
                        (cl-ton:verify-transaction-list answer addr 0 hash))
               (refuses "the list of another account"
                        (cl-ton:verify-transaction-list answer other lt hash))
               (refuses "an empty list for a transaction that exists"
                        (cl-ton:verify-transaction-list (%tx-list-with answer :roots nil :ids (vector)) addr lt hash))
               (refuses "more transactions than were asked for"
                        (cl-ton:verify-transaction-list answer addr lt hash :count 3))
               (refuses "the newest transaction left out (a gap at the head)"
                        (cl-ton:verify-transaction-list
                         (%tx-list-with answer :roots (rest roots) :ids (subseq (cl-ton::tl-get answer :ids) 1))
                         addr lt hash))
               (refuses "a transaction left out of the middle (a broken chain)"
                        (cl-ton:verify-transaction-list
                         (%tx-list-with answer :roots (list (first roots) (third roots) (fourth roots))
                                               :ids (subseq (cl-ton::tl-get answer :ids) 0 3))
                         addr lt hash))
               (refuses "the transactions in the wrong order"
                        (cl-ton:verify-transaction-list
                         (%tx-list-with answer :roots (reverse roots)) addr lt hash))
               (refuses "the newest transaction served twice"
                        (cl-ton:verify-transaction-list
                         (%tx-list-with answer :roots (list (first roots) (first roots))
                                               :ids (subseq (cl-ton::tl-get answer :ids) 0 2))
                         addr lt hash))
               (refuses "a different number of block ids than transactions"
                        (cl-ton:verify-transaction-list
                         (%tx-list-with answer :ids (subseq (cl-ton::tl-get answer :ids) 1)) addr lt hash))
               (refuses "garbage instead of the transactions BOC"
                        (cl-ton:verify-transaction-list
                         (cl-ton::tl-make "liteServer.transactionList" :ids (cl-ton::tl-get answer :ids)
                                          :transactions (coerce (loop repeat 70 collect (%vrnd 256)) '(vector (unsigned-byte 8))))
                         addr lt hash))
               (refuses "an account state cell where a transaction is expected"
                        (cl-ton:verify-transaction-list
                         (%tx-list-with answer :roots (list (getf state :account-cell)) :ids (vector (aref (cl-ton::tl-get answer :ids) 0)))
                         addr lt hash)))
             ;; every single-byte corruption of the served BoC: refused, or harmless
             (let ((octets (cl-ton::tl-get answer :transactions)) (accepted 0) (other-errors 0))
               (dotimes (i 300)
                 (let ((bad (%flip-octet octets (%vrnd (length octets)) (ash 1 (%vrnd 8)))))
                   (handler-case
                       (progn (cl-ton:verify-transaction-list
                               (cl-ton::tl-make "liteServer.transactionList" :ids (cl-ton::tl-get answer :ids) :transactions bad)
                               addr lt hash :count 20)
                              (incf accepted))
                     (cl-ton:proof-error () nil)
                     (error () (incf other-errors)))))
               (check "300 single-bit corruptions of the served transactions: none fails any way but a proof error"
                      (zerop other-errors))
               (check "...and almost none verifies (only a flip the BoC format ignores)" (< accepted 5)))))))))

;;; --- block headers, block data, the transactions of a block -----------------------------

(defun %coins0 (b) (cl-ton:store-bit (cl-ton::store-coins b 0) 0))   ; a CurrencyCollection of nothing

(defun %test-tx (n) (cl-ton:end-cell (cl-ton:store-uint (cl-ton:begin-cell) n 64)))

(defun %inline-into (b root)
  "B with the cell ROOT's data and references appended: a dictionary stored inline."
  (let ((b (cl-ton::store-bits b (cl-ton:cell-bits root) (cl-ton:cell-bit-length root))))
    (loop for r across (cl-ton:cell-refs root) do (setf b (cl-ton:store-ref b r)))
    b))

(defun %block-with-transactions (base accounts)
  "A Block like BASE (a Block cell: the info, value flow and state update are kept) whose account blocks hold
ACCOUNTS, a list of (ACCOUNT-OCTETS (LT . TX-CELL) ...).  The account blocks and the transaction
dictionaries are real ones, apart from the extras of their fork nodes, which no reader here looks at."
  (let* ((update (%test-tx 77))
         (dict (cl-ton::hashmap-cell
                (loop for (account . txs) in accounts
                      collect (cons (cl-ton::octets->uint account)
                                    (let ((tx-dict (cl-ton::hashmap-cell
                                                    (loop for (lt . tx) in txs
                                                          collect (cons lt (let ((tx tx)) (lambda (b) (cl-ton:store-ref (%coins0 b) tx)))))
                                                    64))
                                          (account account))
                                      (lambda (b)
                                        (cl-ton:store-ref
                                         (%inline-into (cl-ton::store-bits (cl-ton:store-uint (%coins0 b) 5 4)
                                                                           (cl-ton::octets->uint account) 256)
                                                       tx-dict)
                                         update)))))
                256))
         (account-blocks (%coins0 (cl-ton:store-ref (cl-ton:store-bit (cl-ton:begin-cell) 1) dict)))
         (extra (cl-ton:end-cell
                 (cl-ton:store-ref
                  (cl-ton:store-ref
                   (cl-ton:store-ref (cl-ton::store-bits (cl-ton:store-uint (cl-ton:begin-cell) #x4a33f6fd 32) 0 513)
                                     (%test-tx 1))
                   (%test-tx 2))
                  (cl-ton:end-cell account-blocks))))
         (refs (coerce (cl-ton:cell-refs base) 'list)))
    (cl-ton:end-cell
     (cl-ton:store-ref (cl-ton:store-ref (cl-ton:store-ref (cl-ton:store-ref
                                                            (cl-ton::store-bits (cl-ton:begin-cell) (cl-ton:cell-bits base)
                                                                                (cl-ton:cell-bit-length base))
                                                            (first refs)) (second refs)) (third refs)) extra))))

(defun test-verify-blocks ()
  (format t "verify: block headers, block data and the transactions of a block~%")
  (if (not (%libs-available-p))
      (skip-missing "block verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 3)
         (let* ((blk (cl-ton::fc-head fc))
                (id (cl-ton::fc-mc-id blk))
                (other-blk (cl-ton::fc-find-block fc (1- (cl-ton::fc-block-seqno blk))))
                (other-id (cl-ton::fc-mc-id other-blk))
                (header (flet ((header-of (id)
                                 (cl-ton::tl-decode
                                  (cl-ton::fc-answer-block-header
                                   fc (cl-ton::tl-make "liteServer.getBlockHeader" :id id :mode 0)))))
                          (header-of id)))
                (other-header (cl-ton::tl-decode
                               (cl-ton::fc-answer-block-header
                                fc (cl-ton::tl-make "liteServer.getBlockHeader" :id other-id :mode 0)))))
           (let ((r (cl-ton:verify-block-header header id)))
             (check "a genuine block header verifies, its BlockInfo is the block's"
                    (and (= (getf (getf r :info) :seqno) (cl-ton::tl-get id :seqno))
                         (= (length (getf r :state-hash)) 32))))
           (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
             (refuses "a header answered for another block than the one asked for"
                      (cl-ton:verify-block-header header other-id))
             (refuses "the header (and its proof) of another block under this block's id"
                      (cl-ton:verify-block-header (%obj-with other-header :id id) id))
             (refuses "this block's id over another block's header proof"
                      (cl-ton:verify-block-header (%obj-with header :header-proof (cl-ton::tl-get other-header :header-proof)) id))
             (refuses "an empty header proof"
                      (cl-ton:verify-block-header (%obj-with header :header-proof (make-array 0 :element-type '(unsigned-byte 8))) id))
             (refuses "garbage as the header proof"
                      (cl-ton:verify-block-header
                       (%obj-with header :header-proof (coerce (loop repeat 80 collect (%vrnd 256)) '(vector (unsigned-byte 8)))) id)))
           ;; block data: the fakechain's own block cell, serialized
           (let* ((cell (cl-ton::fc-block-mc-block blk))
                  (data (cl-ton:serialize-boc cell :has-crc32c nil))
                  (id2 (%obj-with id :root-hash (cl-ton:node-hash cell) :file-hash (cl-ton::sha256 data)))
                  (answer (cl-ton::tl-make "liteServer.blockData" :id id2 :data data)))
             (check "genuine block data verifies: root hash, file hash, Block tag and BlockInfo agree with the id"
                    (= (getf (getf (cl-ton:verify-block-data answer id2) :info) :seqno) (cl-ton::tl-get id :seqno)))
             (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
               (refuses "block data with a file hash that is not the id's"
                        (cl-ton:verify-block-data answer (%obj-with id2 :file-hash (%flip-octet (cl-ton::tl-get id2 :file-hash) 3))))
               (refuses "block data with a root hash that is not the id's"
                        (cl-ton:verify-block-data answer (%obj-with id2 :root-hash (%flip-octet (cl-ton::tl-get id2 :root-hash) 3))))
               (refuses "block data whose id is another block's"
                        (cl-ton:verify-block-data (%obj-with answer :id other-id) id2))
               (refuses "block data of another block served for this id"
                        (cl-ton:verify-block-data
                         (%obj-with answer :data (cl-ton:serialize-boc (cl-ton::fc-block-mc-block other-blk) :has-crc32c nil)) id2))
               (refuses "block data that is not a BOC"
                        (cl-ton:verify-block-data (%obj-with answer :data (make-array 40 :element-type '(unsigned-byte 8) :initial-element 7)) id2))
               (refuses "block data whose BlockInfo is of another seqno than the id"
                        (cl-ton:verify-block-data answer (%obj-with id2 :seqno (1+ (cl-ton::tl-get id2 :seqno)))))))
           ;; the transactions of a block
           (let* ((a1 (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x11))
                  (a2 (make-array 32 :element-type '(unsigned-byte 8) :initial-element #xee))
                  (a3 (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x80))
                  (txs `((,a1 (100 . ,(%test-tx 1)) (105 . ,(%test-tx 2)))
                         (,a2 (200 . ,(%test-tx 3)))
                         (,a3 (300 . ,(%test-tx 4)) (301 . ,(%test-tx 5)) (999 . ,(%test-tx 6)))))
                  (block (%block-with-transactions (cl-ton::fc-block-mc-block blk) txs))
                  (tid (%obj-with id :root-hash (cl-ton:node-hash block)))
                  (proof (cl-ton::fc-proof-boc block))
                  (listing (lambda (entries &key (proof proof) (id tid) (incomplete nil))
                             (cl-ton::tl-make "liteServer.blockTransactions" :id id :req-count 10 :incomplete incomplete
                                              :ids (map 'vector
                                                        (lambda (e)
                                                          (cl-ton::tl-make "liteServer.transactionId" :mode 7
                                                                           :account (first e) :lt (second e)
                                                                           :hash (cl-ton:node-hash (third e))))
                                                        entries)
                                              :proof proof)))
                  (tx (lambda (account lt) (cdr (assoc lt (cdr (assoc account txs :test #'equalp)))))))
             (let* ((all (loop for (account . list) in (sort (copy-list txs) #'< :key (lambda (e) (cl-ton::octets->uint (car e))))
                               append (loop for (lt . cell) in list collect (list account lt cell))))
                    (result (cl-ton:verify-block-transactions (funcall listing all) tid :count 10)))
               (check "every transaction of every account block is found and proved (forks in both dictionaries)"
                      (and (= 6 (length (getf result :transactions))) (null (getf result :incomplete))))
               (check "...in descending order too, and an incomplete flag is passed on"
                      (let ((r (cl-ton:verify-block-transactions (funcall listing (reverse all) :incomplete t) tid :reverse t)))
                        (and (= 6 (length (getf r :transactions))) (getf r :incomplete))))
               (check "a page of the list, and an empty list, need nothing more"
                      (and (= 2 (length (getf (cl-ton:verify-block-transactions (funcall listing (subseq all 2 4)) tid) :transactions)))
                           (null (getf (cl-ton:verify-block-transactions
                                        (funcall listing '() :proof (make-array 0 :element-type '(unsigned-byte 8))) tid)
                                       :transactions))))
               (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
                 (refuses "a listed transaction whose hash is not the block's"
                          (cl-ton:verify-block-transactions
                           (funcall listing (list (list a1 100 (%test-tx 99)))) tid))
                 (refuses "a listed transaction at an lt the block has none at"
                          (cl-ton:verify-block-transactions
                           (funcall listing (list (list a1 101 (funcall tx a1 100)))) tid))
                 (refuses "a listed transaction of an account the block has no account block for"
                          (cl-ton:verify-block-transactions
                           (funcall listing (list (list (make-array 32 :element-type '(unsigned-byte 8) :initial-element 5)
                                                       100 (funcall tx a1 100)))) tid))
                 (refuses "a transaction of one account listed under another's address"
                          (cl-ton:verify-block-transactions
                           (funcall listing (list (list a2 100 (funcall tx a1 100)))) tid))
                 (refuses "transactions served without a proof"
                          (cl-ton:verify-block-transactions
                           (funcall listing all :proof (make-array 0 :element-type '(unsigned-byte 8))) tid))
                 (refuses "the proof of another block"
                          (cl-ton:verify-block-transactions
                           (funcall listing all :proof (cl-ton::fc-proof-boc (cl-ton::fc-block-mc-block blk))) tid))
                 (refuses "the answer of another block than the one asked for"
                          (cl-ton:verify-block-transactions (funcall listing all :id other-id) tid))
                 (refuses "a list out of order"
                          (cl-ton:verify-block-transactions (funcall listing (reverse all)) tid))
                 (refuses "the same transaction twice"
                          (cl-ton:verify-block-transactions (funcall listing (list (first all) (first all))) tid))
                 (refuses "more transactions than were asked for"
                          (cl-ton:verify-block-transactions (funcall listing all) tid :count 5))
                 (refuses "an id without its hash (mode 3)"
                          (cl-ton:verify-block-transactions
                           (cl-ton::tl-make "liteServer.blockTransactions" :id tid :req-count 10 :incomplete nil
                                            :ids (vector (cl-ton::tl-make "liteServer.transactionId" :mode 3 :account a1 :lt 100))
                                            :proof proof)
                           tid))
                 (check "a proof of this very block whose account blocks are pruned away cannot be read through"
                          (let* ((refs (coerce (cl-ton:cell-refs block) 'list))
                                 (extra (fourth refs))
                                 (pruned-extra (cl-ton:end-cell
                                                (cl-ton:store-ref
                                                 (cl-ton:store-ref
                                                  (cl-ton:store-ref (cl-ton::store-bits (cl-ton:begin-cell) (cl-ton:cell-bits extra) (cl-ton:cell-bit-length extra))
                                                                    (svref (cl-ton:cell-refs extra) 0))
                                                  (svref (cl-ton:cell-refs extra) 1))
                                                 (cl-ton::make-pruned-branch (svref (cl-ton:cell-refs extra) 2)))))
                                 (pruned (cl-ton:end-cell
                                          (cl-ton:store-ref (cl-ton:store-ref (cl-ton:store-ref (cl-ton:store-ref
                                                            (cl-ton::store-bits (cl-ton:begin-cell) (cl-ton:cell-bits block) (cl-ton:cell-bit-length block))
                                                            (first refs)) (second refs)) (third refs)) pruned-extra))))
                            (and (equalp (cl-ton::node-hash-at pruned 0) (cl-ton:node-hash block))
                                 (%signals cl-ton:proof-error
                                   (cl-ton:verify-block-transactions
                                    (funcall listing all :proof (cl-ton::fc-proof-boc pruned)) tid)))))))
             ;; every single-bit corruption of the proof BoC: refused or harmless
             (let ((accepted 0) (other 0) (all (list (list a2 200 (funcall tx a2 200)))))
               (dotimes (i 200)
                 (let ((bad (%flip-octet proof (%vrnd (length proof)) (ash 1 (%vrnd 8)))))
                   (handler-case (progn (cl-ton:verify-block-transactions (funcall listing all :proof bad) tid) (incf accepted))
                     (cl-ton:proof-error () nil)
                     (error () (incf other)))))
               (check "200 single-bit corruptions of a block proof: only ever a proof error" (zerop other))
               (check "...and almost none verifies" (< accepted 5)))))))))

;;; --- accounts and getters on a verified state -------------------------------------------------

(defun test-verify-account-run ()
  (format t "verify: an Account cell read, and a getter run on the verified state~%")
  (if (not (%libs-available-p))
      (skip-missing "getter runs (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (cl-ton:wallet-address w))
                (dest (fake-address #x66))
                (absent (fake-address #x88)))
           (dotimes (seqno 3)
             (%fc-enqueue fc (%transfer w seqno dest (cl-ton::nano 1/10)))
             (cl-ton::fakechain-advance fc 2))
           (let* ((blk (cl-ton::fc-head fc))
                  (trusted (cl-ton::fc-mc-id blk))
                  (state (cl-ton:verify-account-state (%served-answer fc blk addr) addr trusted))
                  (cell (getf state :account-cell))
                  (account (cl-ton:parse-account cell)))
             (check "an active wallet: status, address, an lt past the verified last transaction's (the account stores the lt AFTER it), code and data"
                    (and (eq :active (getf account :status))
                         (equalp (cl-ton:address-hash (getf account :address)) (cl-ton:address-hash addr))
                         (< (getf state :last-trans-lt) (getf account :last-trans-lt) (+ 10 (getf state :last-trans-lt)))
                         (getf account :code) (getf account :data) (null (getf account :library-root))))
             (check "...and a balance that is the seeded 10 TON less what three transfers and their fees took"
                    (< (cl-ton::nano 6) (getf account :balance) (cl-ton::nano 10)))
             (check "the getter seqno on the verified account is the number of transfers sent"
                    (equal '(3) (cl-ton:run-account-get-method cell "seqno" '())))
             (check "...and the exit code is 0"
                    (zerop (nth-value 1 (cl-ton:run-account-get-method cell "seqno" '()))))
             (check "an account that does not exist reads as nonexistent and has nothing to run"
                    (let ((r (cl-ton:verify-account-state (%served-answer fc blk absent) absent trusted)))
                      (and (not (getf r :exists))
                           (eq :nonexistent (getf (cl-ton:parse-account (getf r :account-cell)) :status))
                           (handler-case (progn (cl-ton:run-account-get-method (getf r :account-cell) "seqno" '()) nil)
                             (cl-ton::emulator-error () t)))))
             (check "an account without code has nothing to run"
                    (let ((empty (cl-ton:end-cell
                                  (cl-ton::store-bits (cl-ton:begin-cell) 0 0))))
                      (declare (ignorable empty))
                      (handler-case (progn (cl-ton:run-account-get-method
                                            (getf (cl-ton:verify-account-state
                                                   (%served-answer fc blk dest) dest trusted)
                                                  :account-cell)
                                            "seqno" '())
                                           nil)
                        (cl-ton::emulator-error () t))))
             (check "a method the contract does not have ends with TVM exit code 11, which the caller must look at"
                    (= 11 (nth-value 1 (cl-ton:run-account-get-method cell "no_such_method" '()))))
             (flet ((acct (layout state &key (balance 12345678901))
                      ;; an Account cell in the old StorageInfo layout (:old, :old-public) or the newer (:new-none, :new-info)
                      (let ((b (cl-ton:begin-cell)) (code (cl-ton:end-cell (cl-ton:store-uint (cl-ton:begin-cell) #xC0DE 16)))
                            (data (cl-ton:end-cell (cl-ton:store-uint (cl-ton:begin-cell) #xDA7A 16))))
                        (flet ((u (v n) (setf b (cl-ton:store-uint b v n))))
                          (u 1 1) (u #b100 3) (u 0 8) (u (+ (expt 2 200) 77) 256)       ; account$1, addr_std, wc 0
                          (u 1 3) (u 9 8) (u 2 3) (u 4096 16)                            ; used: cells 9, bits 4096
                          (ecase layout
                            (:old (u 0 3))
                            (:old-public (u 1 3) (u 1 8))
                            (:new-none (u 0 3))
                            (:new-info (u 1 3) (u (+ (expt 2 250) 5) 256)))
                          (u 1700000000 32) (u 0 1)                                     ; last_paid, no due_payment
                          (u 31 64) (u 5 4) (u balance 40) (u 0 1)                       ; last_trans_lt, coins, no extra currencies
                          (ecase state
                            (:active (u 1 1) (u 0 1) (u 0 1) (u 1 1) (u 1 1) (u 0 1)
                             (setf b (cl-ton:store-ref (cl-ton:store-ref b code) data)))
                            (:frozen (u 0 1) (u 1 1) (u (+ (expt 2 240) 9) 256))
                            (:uninit (u 0 2))))
                        (cl-ton:end-cell b))))
               (dolist (layout '(:old :old-public :new-none :new-info))
                 (let ((a (cl-ton:parse-account (acct layout :active))))
                   (check (format nil "an active account in the ~(~A~) StorageInfo layout reads as active, with its balance, code and data" layout)
                          (and (eq :active (getf a :status)) (= 12345678901 (getf a :balance)) (= 31 (getf a :last-trans-lt))
                               (getf a :code) (getf a :data) (null (getf a :library-root))))))
               (check "a FROZEN account in the new layout with a storage_extra dict hash reads as frozen, with its hash"
                      (let ((a (cl-ton:parse-account (acct :new-info :frozen))))
                        (and (eq :frozen (getf a :status)) (= 12345678901 (getf a :balance))
                             (= (+ (expt 2 240) 9) (cl-ton::octets->uint (getf a :frozen-hash))))))
               (check "...and an uninit one in either layout reads as uninit"
                      (every (lambda (l) (eq :uninit (getf (cl-ton:parse-account (acct l :uninit)) :status)))
                             '(:old :new-info))))
             (let ((other 0) (parsed 0))
               (dotimes (i 300)
                 (let* ((n (1+ (%vrnd 200)))
                        (junk (cl-ton:end-cell (cl-ton::store-bits (cl-ton:begin-cell) (%vrnd (expt 2 n)) n))))
                   (handler-case (progn (cl-ton:parse-account junk) (incf parsed))
                     (cl-ton:proof-error () nil)
                     (error () (incf other)))))
               (check "300 random cells read as accounts: only ever a proof error or a reading" (zerop other)))))))))

;;; --- libraries and sent messages -----------------------------------------------------------

(defun test-verify-libraries ()
  (format t "verify: library results, the status of a sent message, the hash of a message~%")
  (flet ((lib (n) (cl-ton:end-cell (cl-ton:store-ref (cl-ton:store-uint (cl-ton:begin-cell) n 32) (%test-tx n))))
         (answer (&rest entries)
           (cl-ton::tl-make "liteServer.libraryResult"
                            :result (map 'vector
                                         (lambda (e)
                                           (cl-ton::tl-make "liteServer.libraryEntry" :hash (car e)
                                                                                       :data (cl-ton:serialize-boc (cdr e))))
                                         entries))))
    (let* ((a (lib 1)) (b (lib 2)) (c (lib 3))
           (ha (cl-ton:node-hash a)) (hb (cl-ton:node-hash b)) (hc (cl-ton:node-hash c))
           (asked (list ha hb)))
      (check "the libraries asked for, each of which hashes to its hash, verify"
             (let ((r (cl-ton:verify-libraries (answer (cons ha a) (cons hb b)) asked)))
               (and (= 2 (length r)) (equalp (car (first r)) ha) (equalp (cl-ton:node-hash (cdr (second r))) hb))))
      (check "a library the chain lacks may be left out, and an empty answer is fine"
             (and (= 1 (length (cl-ton:verify-libraries (answer (cons hb b)) asked)))
                  (null (cl-ton:verify-libraries (answer) asked))))
      (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
        (refuses "a library that was not asked for" (cl-ton:verify-libraries (answer (cons hc c)) asked))
        (refuses "a library served twice" (cl-ton:verify-libraries (answer (cons ha a) (cons ha a)) asked))
        (refuses "another library's cell under an asked-for hash" (cl-ton:verify-libraries (answer (cons ha b)) asked))
        (refuses "a library whose data is not a BOC"
                 (cl-ton:verify-libraries
                  (cl-ton::tl-make "liteServer.libraryResult"
                                   :result (vector (cl-ton::tl-make "liteServer.libraryEntry" :hash ha
                                                                    :data (make-array 30 :element-type '(unsigned-byte 8) :initial-element 9))))
                  asked))
        (refuses "a library whose data is empty"
                 (cl-ton:verify-libraries
                  (cl-ton::tl-make "liteServer.libraryResult"
                                   :result (vector (cl-ton::tl-make "liteServer.libraryEntry" :hash ha
                                                                    :data (make-array 0 :element-type '(unsigned-byte 8)))))
                  asked))))
    (check "a sent message with status 1 is accepted, any other status is an error"
           (and (= 1 (cl-ton:check-send-message-status (cl-ton::tl-make "liteServer.sendMsgStatus" :status 1)))
                (handler-case (progn (cl-ton:check-send-message-status (cl-ton::tl-make "liteServer.sendMsgStatus" :status 0)) nil)
                  (cl-ton:ton-error () t))))
    (check "the hash of a message is the hash of its root cell; a BOC with two roots has none"
           (let ((m (%test-tx 42)))
             (and (equalp (cl-ton:external-message-hash (cl-ton:serialize-boc m)) (cl-ton:node-hash m))
                  (%signals cl-ton:proof-error
                    (cl-ton:external-message-hash (cl-ton::fc-cells-boc (list m (%test-tx 43))))))))
    (if (not (%libs-available-p))
        (skip-missing "library answer of the fakechain (emulator shared library)")
        (call-with-fc-session
         (lambda (fc tl proxy cfg)
           (declare (ignore tl proxy cfg))
           (let* ((lib (%test-tx 1234))
                  (hex (cl-ton::fakechain-add-library fc lib))
                  (hash (cl-ton:node-hash lib))
                  (reply (cl-ton::tl-decode
                          (cl-ton::fc-answer-get-libraries
                           fc (cl-ton::tl-make "liteServer.getLibraries" :library-list (vector hash))))))
             (declare (ignorable hex))
             (check "the fakechain's own library answer verifies"
                    (equalp (cl-ton:node-hash (cdr (first (cl-ton:verify-libraries reply (list hash))))) hash))))))))

;;; --- the shards of a masterchain block -----------------------------------------------------

(defun test-verify-shards ()
  (format t "verify: getAllShardsInfo, against the block's McBlockExtra, and against real tonlib~%")
  (if (not (%libs-available-p))
      (skip-missing "all-shards verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore proxy cfg))
         (cl-ton::fakechain-advance fc 3)
         (let* ((blk (cl-ton::fc-head fc))
                (id (cl-ton::fc-mc-id blk))
                (other-blk (cl-ton::fc-find-block fc (1- (cl-ton::fc-block-seqno blk))))
                (other-id (cl-ton::fc-mc-id other-blk))
                (ask (lambda (id) (cl-ton::tl-decode
                                   (cl-ton::fc-answer-all-shards-info fc (cl-ton::tl-make "liteServer.getAllShardsInfo" :id id)))))
                (answer (funcall ask id))
                (other (funcall ask other-id))
                (result (cl-ton:verify-all-shards-info answer id))
                (shard (first (getf result :shards))))
           (check "the masterchain block's one shard: workchain 0, the whole shard, this block's seqno and hashes"
                  (and (= 1 (length (getf result :shards)))
                       (= 0 (getf shard :workchain)) (= #x8000000000000000 (getf shard :shard))
                       (= (cl-ton::fc-block-seqno blk) (getf shard :seqno))
                       (equalp (getf shard :root-hash) (cl-ton::fc-block-sh-root blk))
                       (equalp (getf shard :file-hash) (cl-ton::fc-block-sh-file blk))))
           (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
             (refuses "an answer for another block than the one asked for" (cl-ton:verify-all-shards-info answer other-id))
             (refuses "another block's shards under this block's id"
                      (cl-ton:verify-all-shards-info (%obj-with other :id id) id))
             (refuses "another block's ShardHashes served with this block's proof"
                      (cl-ton:verify-all-shards-info (%obj-with answer :data (cl-ton::tl-get other :data)) id))
             (refuses "this block's ShardHashes with another block's proof"
                      (cl-ton:verify-all-shards-info (%obj-with answer :proof (cl-ton::tl-get other :proof)) id))
             (refuses "an empty ShardHashes served for a non-empty one"
                      (cl-ton:verify-all-shards-info
                       (%obj-with answer :data (cl-ton::boc-of (cl-ton:end-cell (cl-ton:store-bit (cl-ton:begin-cell) 0)))) id))
             (refuses "the header proof of the block, which cannot be read down to its McBlockExtra"
                      (cl-ton:verify-all-shards-info
                       (%obj-with answer :proof (cl-ton::fc-proof-boc (cl-ton::fc-header-proof-node (cl-ton::fc-block-mc-block blk)))) id))
             (refuses "garbage as the data"
                      (cl-ton:verify-all-shards-info
                       (%obj-with answer :data (coerce (loop repeat 60 collect (%vrnd 256)) '(vector (unsigned-byte 8)))) id)))
           (let ((proof (cl-ton::tl-get answer :proof)) (accepted 0) (other-errors 0))
             (dotimes (i 200)
               (let ((bad (%flip-octet proof (%vrnd (length proof)) (ash 1 (%vrnd 8)))))
                 (handler-case (progn (cl-ton:verify-all-shards-info (%obj-with answer :proof bad) id) (incf accepted))
                   (cl-ton:proof-error () nil)
                   (error () (incf other-errors)))))
             (check "200 single-bit corruptions of the proof: only ever a proof error" (zerop other-errors))
             (check "...and almost none verifies" (< accepted 5)))
           ;; the lite client path, over ADNL-ext
           (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                  (client (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc))))
             (unwind-protect
                  (progn (loop repeat 100 until (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl client)) do (sleep 0.1))
                         (let ((r (cl-ton:lite-shards client)))
                           (check "lite-shards: the proved head's shards over ADNL-ext"
                                  (and (= 1 (length (getf r :shards)))
                                       (= (cl-ton::tl-get (getf r :mc-block) :seqno) (cl-ton::fc-head-seqno fc))))))
               (cl-ton:close-lite-client client)))
           ;; real tonlib is the oracle: it checks the same proof against the same block
           (let* ((info (let ((found nil))
                          (%until (lambda ()
                                    (let ((r (%typed-call tl (cl-ton:tlapi-make "blocks.getMasterchainInfo"))))
                                      (when (cl-ton:tlapi-is r "blocks.masterchainInfo") (setf found r) t)))
                                  :seconds 15 :each (lambda () nil))
                          found))
                  (last (and info (cl-ton:tlapi-get info :last)))
                  (r (and last (%typed-call tl (cl-ton:tlapi-make "blocks.getShards" :id last)))))
             (check "real tonlib accepts the fakechain's allShardsInfo: blocks.getShards names the same shard block"
                    (and r (cl-ton:tlapi-is r "blocks.shards")
                         (let* ((shards (cl-ton:tlapi-get r :shards))
                                (s (first shards))
                                (head (cl-ton::fc-find-block fc (cl-ton:tlapi-get last :seqno))))
                           (and (= 1 (length shards))
                                (= (cl-ton:tlapi-get s :seqno) (cl-ton::fc-block-seqno head))
                                (equalp (cl-ton:tlapi-get s :root-hash) (cl-ton::fc-block-sh-root head))))))))))))

(defun test-verify ()
  (test-dict-lookup)
  (test-verify-account-state)
  (test-verify-transactions)
  (test-verify-blocks)
  (test-verify-account-run)
  (test-verify-libraries)
  (test-verify-shards)
  (test-shard-lookup)
  (test-verify-shard-info)
  (test-verify-lookup-block)
  (test-verify-lookup-block-plain)
  (test-verify-real-liteserver-shapes)
  (test-link-vectors)
  (test-verify-back-link)
  (test-verify-libraries-with-proof)
  (test-mutation-matrix)
  (test-mutation-matrix-2)
  (test-verify-fuzz))

;;; --- getShardInfo ---------------------------------------------------------------------------

(defun %bt-fork (left right)
  (cl-ton:end-cell (cl-ton:store-ref (cl-ton:store-ref (cl-ton:store-bit (cl-ton:begin-cell) 1) left) right)))

(defun %shard-hashes-of (entries)
  "A ShardHashes dictionary root over ENTRIES, a list of (WORKCHAIN . BINTREE-ROOT)."
  (cl-ton::hashmap-cell (mapcar (lambda (e) (cons (ldb (byte 32 0) (car e))
                                                  (let ((c (cdr e))) (lambda (b) (cl-ton:store-ref b c)))))
                                entries)
                        32))

(defun test-shard-lookup ()
  (format t "verify: the shard lookup of getShardInfo over hand-built shard trees~%")
  (let* ((h (lambda (n) (make-array 32 :element-type '(unsigned-byte 8) :initial-element n)))
         (leaf (lambda (seqno) (cl-ton::%bt-leaf :seqno seqno :reg-mc-seqno 1 :start-lt 10 :end-lt 20
                                                 :root-hash (funcall h seqno) :file-hash (funcall h (1+ seqno))
                                                 :gen-utime 5)))
         (l00 (funcall leaf 1)) (l01 (funcall leaf 2)) (l1 (funcall leaf 3))
         ;; workchain 0: ((00 01) 1); workchain 7: one leaf, the whole workchain
         (tree (%bt-fork (%bt-fork l00 l01) l1))
         (root (%shard-hashes-of (list (cons 0 tree) (cons 7 (funcall leaf 9)))))
         (look (lambda (wc shard exact)
                 (multiple-value-bind (cell true) (cl-ton:lookup-shard-leaf root wc shard exact)
                   (and cell (list (cl-ton:node-hash cell) true))))))
    (check "a leaf asked for by its own id is found, exact or not"
           (and (equalp (funcall look 0 #x2000000000000000 t) (list (cl-ton:node-hash l00) #x2000000000000000))
                (equalp (funcall look 0 #x6000000000000000 nil) (list (cl-ton:node-hash l01) #x6000000000000000))
                (equalp (funcall look 0 #xC000000000000000 t) (list (cl-ton:node-hash l1) #xC000000000000000))))
    (check "a shard INSIDE a leaf finds that leaf unless exact is asked"
           (and (equalp (funcall look 0 #x1000000000000000 nil) (list (cl-ton:node-hash l00) #x2000000000000000))
                (null (funcall look 0 #x1000000000000000 t))
                (equalp (funcall look 0 #xE000000000000000 nil) (list (cl-ton:node-hash l1) #xC000000000000000))
                (null (funcall look 0 #xE000000000000000 t))))
    (check "a shard ABOVE several leaves (the workchain, or the left half) finds nothing"
           (and (null (funcall look 0 #x8000000000000000 nil)) (null (funcall look 0 #x8000000000000000 t))
                (null (funcall look 0 #x4000000000000000 nil))))
    (check "a workchain that is a single leaf: whole shard found, a half of it only without exact"
           (and (equalp (funcall look 7 #x8000000000000000 t) (list (cl-ton:node-hash (funcall leaf 9)) #x8000000000000000))
                (equalp (funcall look 7 #x4000000000000000 nil) (list (cl-ton:node-hash (funcall leaf 9)) #x8000000000000000))
                (null (funcall look 7 #x4000000000000000 t))))
    (check "the masterchain, a workchain without shards and the zero shard find nothing"
           (and (null (funcall look -1 #x8000000000000000 nil)) (null (funcall look 5 #x8000000000000000 nil))
                (null (funcall look 0 0 nil))))
    (check "an empty ShardHashes finds nothing"
           (null (cl-ton:lookup-shard-leaf nil 0 #x8000000000000000 nil)))
    (check "a fork that is not two references is refused"
           (%signals cl-ton:proof-error
             (cl-ton:lookup-shard-leaf
              (%shard-hashes-of (list (cons 0 (cl-ton:end-cell (cl-ton:store-ref (cl-ton:store-bit (cl-ton:begin-cell) 1) l00)))))
              0 #x2000000000000000 nil)))))

(defun test-verify-shard-info ()
  (format t "verify: getShardInfo, against the masterchain state, and over ADNL-ext~%")
  (if (not (%libs-available-p))
      (skip-missing "shard-info verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 3)
         (let* ((blk (cl-ton::fc-head fc))
                (id (cl-ton::fc-mc-id blk))
                (other-blk (cl-ton::fc-find-block fc (1- (cl-ton::fc-block-seqno blk))))
                (other-id (cl-ton::fc-mc-id other-blk))
                (whole (- (expt 2 63)))
                (ask (lambda (id wc shard exact)
                       (cl-ton::tl-decode
                        (cl-ton::fc-answer-shard-info
                         fc (cl-ton::tl-make "liteServer.getShardInfo" :id id :workchain wc :shard shard :exact exact)))))
                (found (funcall ask id 0 whole t))
                (found-other (funcall ask other-id 0 whole t))
                (none (funcall ask id 0 (- (expt 2 62)) t))
                (r (cl-ton:verify-shard-info found id 0 #x8000000000000000 :exact t)))
           (check "the one shard: found, with this block's shard block seqno and hashes"
                  (and (getf r :found) (= #x8000000000000000 (getf r :shard))
                       (= (cl-ton::fc-block-seqno blk) (getf r :seqno))
                       (equalp (getf r :root-hash) (cl-ton::fc-block-sh-root blk))
                       (equalp (getf r :file-hash) (cl-ton::fc-block-sh-file blk))))
           (check "a half of it asked exactly: the proof shows there is no such shard"
                  (let ((x (cl-ton:verify-shard-info none id 0 #x4000000000000000 :exact t))) (and x (not (getf x :found)))))
           (check "...and without exact it is the whole shard again"
                  (getf (cl-ton:verify-shard-info (funcall ask id 0 (- (expt 2 62)) nil) id 0 #x4000000000000000)
                        :found))
           (check "the masterchain and a workchain without shards: no shard, proved"
                  (and (not (getf (cl-ton:verify-shard-info (funcall ask id -1 whole nil) id -1 #x8000000000000000) :found))
                       (not (getf (cl-ton:verify-shard-info (funcall ask id 5 whole nil) id 5 #x8000000000000000) :found))))
           (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
             (refuses "an answer for another block than the one asked for"
                      (cl-ton:verify-shard-info found other-id 0 #x8000000000000000 :exact t))
             (refuses "another block's answer under this block's id"
                      (cl-ton:verify-shard-info (%obj-with found-other :id id) id 0 #x8000000000000000 :exact t))
             (refuses "this block's answer with another block's proof"
                      (cl-ton:verify-shard-info (%obj-with found :shard-proof (cl-ton::tl-get found-other :shard-proof))
                                                id 0 #x8000000000000000 :exact t))
             (refuses "another block's shard description (another leaf) served with this block's proof"
                      (cl-ton:verify-shard-info (%obj-with found :shard-descr (cl-ton::tl-get found-other :shard-descr))
                                                id 0 #x8000000000000000 :exact t))
             (refuses "a shard block with another seqno than the proof names"
                      (cl-ton:verify-shard-info
                       (%obj-with found :shardblk (cl-ton::tl-block-id-ext :workchain 0 :shard whole :seqno 1
                                                                           :root-hash (cl-ton::fc-block-sh-root blk)
                                                                           :file-hash (cl-ton::fc-block-sh-file blk)))
                       id 0 #x8000000000000000 :exact t))
             (refuses "a shard block of the other shard's hashes"
                      (cl-ton:verify-shard-info (%obj-with found :shardblk (cl-ton::tl-get found-other :shardblk))
                                                id 0 #x8000000000000000 :exact t))
             (refuses "no shard served where the proof shows one"
                      (cl-ton:verify-shard-info none id 0 #x8000000000000000 :exact t))
             (refuses "an empty description where the proof shows a leaf"
                      (cl-ton:verify-shard-info (%obj-with found :shard-descr (make-array 0 :element-type '(unsigned-byte 8)))
                                                id 0 #x8000000000000000 :exact t))
             (refuses "a shard served where the proof shows none (exact half-shard)"
                      (cl-ton:verify-shard-info (%obj-with none :shardblk (cl-ton::tl-get found :shardblk)
                                                                :shard-descr (cl-ton::tl-get found :shard-descr))
                                                id 0 #x4000000000000000 :exact t))
             (refuses "a description served with the 'no shard' id"
                      (cl-ton:verify-shard-info (%obj-with none :shard-descr (cl-ton::tl-get found :shard-descr))
                                                id 0 #x4000000000000000 :exact t))
             (refuses "the answer to another question (workchain 5) taken for this one"
                      (cl-ton:verify-shard-info found id 5 #x8000000000000000 :exact t))
             (refuses "an empty proof"
                      (cl-ton:verify-shard-info (%obj-with found :shard-proof (make-array 0 :element-type '(unsigned-byte 8)))
                                                id 0 #x8000000000000000 :exact t))
             (refuses "garbage as the description"
                      (cl-ton:verify-shard-info
                       (%obj-with found :shard-descr (coerce (loop repeat 60 collect (%vrnd 256)) '(vector (unsigned-byte 8))))
                       id 0 #x8000000000000000 :exact t)))
           (let ((proof (cl-ton::tl-get found :shard-proof)) (accepted 0) (other-errors 0))
             (dotimes (i 200)
               (let ((bad (%flip-octet proof (%vrnd (length proof)) (ash 1 (%vrnd 8)))))
                 (handler-case (progn (cl-ton:verify-shard-info (%obj-with found :shard-proof bad) id 0 #x8000000000000000 :exact t)
                                      (incf accepted))
                   (cl-ton:proof-error () nil)
                   (error () (incf other-errors)))))
             (check "200 single-bit corruptions of the shard proof: only ever a proof error" (zerop other-errors))
             (check "...and almost none verifies" (< accepted 5)))
           (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                  (client (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc))))
             (unwind-protect
                  (progn (loop repeat 100 until (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl client)) do (sleep 0.1))
                         (let ((x (cl-ton:lite-shard-info client 0 #x8000000000000000 :exact t)))
                           (check "lite-shard-info: the proved head's shard block over ADNL-ext"
                                  (and (getf x :found) (= (getf x :seqno) (cl-ton::fc-head-seqno fc)))))
                         (check "...and a shard that is not there is reported as not found"
                                (not (getf (cl-ton:lite-shard-info client 3 #x8000000000000000) :found))))
               (cl-ton:close-lite-client client))))))))

;;; --- lookupBlockWithProof -------------------------------------------------------------------

(defun test-verify-lookup-block ()
  (format t "verify: lookupBlockWithProof, against the trusted masterchain block, and over ADNL-ext~%")
  (if (not (%libs-available-p))
      (skip-missing "block lookup verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 6)
         (let* ((head (cl-ton::fc-head fc))
                (head-id (cl-ton::fc-mc-id head))
                (b3 (cl-ton::fc-find-block fc 3)) (b4 (cl-ton::fc-find-block fc 4)) (b5 (cl-ton::fc-find-block fc 5))
                (whole #x8000000000000000)
                (ask (lambda (trusted wc mode &key (seqno 0) lt utime)
                       (cl-ton::tl-decode
                        (cl-ton::fc-answer-lookup-block
                         fc (apply #'cl-ton::tl-make "liteServer.lookupBlockWithProof"
                                   :mode mode
                                   :id (cl-ton::tl-make "tonNode.blockId" :workchain wc :shard (- whole (expt 2 64)) :seqno seqno)
                                   :mc-block-id trusted
                                   (append (and lt (list :lt lt)) (and utime (list :utime utime))))))))
                (verify (lambda (answer trusted wc mode &key (seqno 0) (lt 0) (utime 0))
                          (cl-ton:verify-lookup-block answer trusted wc whole mode :seqno seqno :lt lt :utime utime)))
                (seq-of (lambda (r) (cl-ton::tl-get (getf r :block-id) :seqno))))
           (check "by seqno, workchain 0, the trusted head itself: no proof of a prev_blocks entry needed"
                  (let* ((a (funcall ask head-id 0 1 :seqno (cl-ton::fc-block-seqno head)))
                         (r (funcall verify a head-id 0 1 :seqno (cl-ton::fc-block-seqno head))))
                    (and (= (funcall seq-of r) (cl-ton::fc-block-seqno head))
                         (equalp (cl-ton::tl-get (getf r :block-id) :root-hash) (cl-ton::fc-block-sh-root head)))))
           (let* ((a3 (funcall ask head-id 0 1 :seqno 3))
                  (r3 (funcall verify a3 head-id 0 1 :seqno 3)))
             (check "by seqno, an OLDER block: its masterchain block is in the trusted state's prev_blocks"
                    (and (= 3 (funcall seq-of r3)) (= 3 (cl-ton::tl-get (getf r3 :mc-block) :seqno))
                         (equalp (cl-ton::tl-get (getf r3 :block-id) :root-hash) (cl-ton::fc-block-sh-root b3))))
             (check "by seqno in the masterchain: the block itself, no links"
                    (let* ((a (funcall ask head-id -1 1 :seqno 3)) (r (funcall verify a head-id -1 1 :seqno 3)))
                      (and (= 0 (length (cl-ton::tl-get a :shard-links)))
                           (equalp (cl-ton::tl-get (getf r :block-id) :root-hash) (cl-ton::fc-block-mc-root b3)))))
             (check "a proof chain of several shard blocks (the masterchain block is 2 blocks after the answer)"
                    (let ((cl-ton::*fc-lookup-alt-seqno* 5))
                      (let* ((a (funcall ask head-id 0 1 :seqno 3)) (r (funcall verify a head-id 0 1 :seqno 3)))
                        (and (= 3 (length (cl-ton::tl-get a :shard-links)))
                             (= 5 (cl-ton::tl-get (getf r :mc-block) :seqno)) (= 3 (funcall seq-of r))))))
             (check "by logical time: the block whose lt range holds it, proved by its predecessor's end_lt"
                    (let* ((lt (1+ (cl-ton::fc-block-start-lt b4)))
                           (a (funcall ask head-id 0 2 :lt lt)) (r (funcall verify a head-id 0 2 :lt lt)))
                      (and (= 4 (funcall seq-of r))
                           (= 4 (funcall seq-of (funcall verify (funcall ask head-id -1 2 :lt lt) head-id -1 2 :lt lt))))))
             (check "by unix time: the first block generated at or after it"
                    (let* ((u (cl-ton::fc-block-utime b4))
                           (a (funcall ask head-id 0 4 :utime u)) (r (funcall verify a head-id 0 4 :utime u)))
                      (and (= 4 (funcall seq-of r))
                           (= 4 (funcall seq-of (funcall verify (funcall ask head-id 0 4 :utime (1- u)) head-id 0 4 :utime (1- u)))))))
             (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
               (refuses "a bad mode (no or several of the seqno, lt, utime bits)"
                        (cl-ton:verify-lookup-block a3 head-id 0 whole 7 :seqno 3))
               (refuses "an answer for another seqno than the one asked for"
                        (funcall verify a3 head-id 0 1 :seqno 4))
               (refuses "another workchain than the one asked for"
                        (funcall verify a3 head-id 5 1 :seqno 3))
               (refuses "another block's id served for this chain"
                        (funcall verify (%obj-with a3 :id (cl-ton::fc-sh-id b4)) head-id 0 1 :seqno 3))
               (refuses "a masterchain block that the trusted block does not list (a made-up id)"
                        (funcall verify (%obj-with a3 :mc-block-id
                                                   (cl-ton::tl-block-id-ext :seqno 3 :root-hash (cl-ton::fc-block-sh-root b3)
                                                                            :file-hash (cl-ton::fc-block-mc-file b3)))
                                 head-id 0 1 :seqno 3))
               (refuses "the answer checked against another trusted block than the one it was asked with"
                        (funcall verify a3 (cl-ton::fc-mc-id b5) 0 1 :seqno 3))
               (refuses "no links: the masterchain block is not the shard block answered"
                        (funcall verify (%obj-with a3 :shard-links (vector)) head-id 0 1 :seqno 3))
               (refuses "a link to a shard block the masterchain does not name"
                        (funcall verify (%obj-with a3 :shard-links
                                                   (vector (cl-ton::tl-make "liteServer.shardBlockLink" :id (cl-ton::fc-sh-id b4)
                                                                            :proof (cl-ton::tl-get (aref (cl-ton::tl-get a3 :shard-links) 0) :proof))))
                                 head-id 0 1 :seqno 3))
               (refuses "another block's link proof"
                        (funcall verify (%obj-with a3 :shard-links
                                                   (vector (cl-ton::tl-make "liteServer.shardBlockLink" :id (cl-ton::fc-sh-id b3)
                                                                            :proof (cl-ton::tl-get (aref (cl-ton::tl-get (funcall ask head-id 0 1 :seqno 4) :shard-links) 0) :proof))))
                                 head-id 0 1 :seqno 3))
               (refuses "another block's header"
                        (funcall verify (%obj-with a3 :header (cl-ton::tl-get (funcall ask head-id 0 1 :seqno 4) :header))
                                 head-id 0 1 :seqno 3))
               (refuses "the client state proof of another block"
                        (funcall verify (%obj-with a3 :client-mc-state-proof
                                                   (cl-ton::fc-proof-boc (cl-ton::fc-header-proof-node (cl-ton::fc-block-mc-block b5))))
                                 head-id 0 1 :seqno 3))
               (refuses "an empty header" (funcall verify (%obj-with a3 :header (make-array 0 :element-type '(unsigned-byte 8))) head-id 0 1 :seqno 3))
               (let* ((lt (1+ (cl-ton::fc-block-start-lt b4))) (al (funcall ask head-id 0 2 :lt lt)))
                 (refuses "a time lookup whose lt is past the block's end_lt"
                          (funcall verify al head-id 0 2 :lt (+ 1000 (cl-ton::fc-block-end-lt b4))))
                 (refuses "a time lookup whose lt is before the predecessor's end_lt"
                          (funcall verify al head-id 0 2 :lt (1- (cl-ton::fc-block-start-lt b4))))
                 (refuses "a time lookup without the predecessor's header"
                          (funcall verify (%obj-with al :prev-header (make-array 0 :element-type '(unsigned-byte 8)))
                                   head-id 0 2 :lt lt))
                 (refuses "a time lookup with an unrelated block as the predecessor's header"
                          (funcall verify (%obj-with al :prev-header (cl-ton::tl-get al :header)) head-id 0 2 :lt lt))))
             (dolist (field '(:header :client-mc-state-proof :mc-block-proof))
               (let ((data (cl-ton::tl-get a3 field)) (accepted 0) (other 0))
                 (dotimes (i 120)
                   (let ((bad (%flip-octet data (%vrnd (length data)) (ash 1 (%vrnd 8)))))
                     (handler-case (progn (funcall verify (%obj-with a3 field bad) head-id 0 1 :seqno 3) (incf accepted))
                       (cl-ton:proof-error () nil)
                       (error () (incf other)))))
                 (check (format nil "120 single-bit corruptions of the ~(~A~): only ever a proof error, almost none verifies" field)
                        (and (zerop other) (< accepted 5))))))
           (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                  (client (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc))))
             (unwind-protect
                  (progn (loop repeat 100 until (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl client)) do (sleep 0.1))
                         (check "lite-lookup-block over ADNL-ext: by seqno, and by logical time"
                                (and (= 3 (cl-ton::tl-get (getf (cl-ton:lite-lookup-block client 0 whole :seqno 3) :block-id) :seqno))
                                     (= 4 (cl-ton::tl-get (getf (cl-ton:lite-lookup-block client 0 whole :lt (1+ (cl-ton::fc-block-start-lt b4)))
                                                                :block-id)
                                                          :seqno))))
                         (check "...and a block that does not exist is a liteserver error"
                                (handler-case (progn (cl-ton:lite-lookup-block client 0 whole :seqno 9999) nil)
                                  (cl-ton:lite-error () t))))
               (cl-ton:close-lite-client client))))))))

;;; --- block lookup on a liteserver without lookupBlockWithProof -------------------------------

(defun test-verify-lookup-block-plain ()
  (format t "verify: block lookup without lookupBlockWithProof (lookupBlock, getShardBlockProof, getBlockProof)~%")
  (if (not (%libs-available-p))
      (skip-missing "plain block lookup (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 6)
         (let* ((b3 (cl-ton::fc-find-block fc 3)) (b4 (cl-ton::fc-find-block fc 4))
                (whole #x8000000000000000)
                (signed (- whole (expt 2 64)))
                (plain (lambda (wc mode &key (seqno 0) lt utime)
                         (cl-ton::tl-decode
                          (cl-ton::fc-answer-lookup-block-plain
                           fc (apply #'cl-ton::tl-make "liteServer.lookupBlock" :mode mode
                                     :id (cl-ton::tl-make "tonNode.blockId" :workchain wc :shard signed :seqno seqno)
                                     (append (and lt (list :lt lt)) (and utime (list :utime utime))))))))
                (shard-proof (lambda (id)
                               (cl-ton::tl-decode (cl-ton::fc-answer-shard-block-proof
                                                   fc (cl-ton::tl-make "liteServer.getShardBlockProof" :id id)))))
                (refused (lambda (thunk) (handler-case (progn (funcall thunk) nil) (cl-ton:proof-error () t))))
                (seq-of (lambda (id) (cl-ton::tl-get id :seqno))))
           ;; the header of a plain lookup
           (check "verify-lookup-header: the block found by seqno"
                  (= 3 (funcall seq-of (getf (cl-ton:verify-lookup-header (funcall plain 0 1 :seqno 3) 0 whole 1 :seqno 3) :block-id))))
           (check "...refuses another seqno than asked for"
                  (funcall refused (lambda () (cl-ton:verify-lookup-header (funcall plain 0 1 :seqno 4) 0 whole 1 :seqno 3))))
           (check "...refuses another workchain than asked for"
                  (funcall refused (lambda () (cl-ton:verify-lookup-header (funcall plain 0 1 :seqno 3) -1 whole 1 :seqno 3))))
           (check "...refuses the header proof of another block"
                  (funcall refused (lambda ()
                                     (cl-ton:verify-lookup-header
                                      (%obj-with (funcall plain 0 1 :seqno 3) :header-proof
                                                 (cl-ton::tl-get (funcall plain 0 1 :seqno 4) :header-proof))
                                      0 whole 1 :seqno 3))))
           (check "...refuses an empty header proof"
                  (funcall refused (lambda ()
                                     (cl-ton:verify-lookup-header
                                      (%obj-with (funcall plain 0 1 :seqno 3) :header-proof (make-array 0 :element-type '(unsigned-byte 8)))
                                      0 whole 1 :seqno 3))))
           ;; by logical time: the predecessor's header closes the argument
           (let* ((lt (1+ (cl-ton::fc-block-start-lt b4)))
                  (al (funcall plain 0 2 :lt lt))
                  (found (cl-ton:verify-lookup-header al 0 whole 2 :lt lt))
                  (prev (find-if (lambda (p) (= (getf p :seqno) 3)) (getf found :prev)))
                  (prev-id (cl-ton::tl-block-id-ext :workchain (getf prev :workchain) :shard signed :seqno 3
                                                    :root-hash (getf prev :root-hash) :file-hash (getf prev :file-hash)))
                  (prev-answer (cl-ton::tl-decode (cl-ton::fc-answer-block-header
                                                   fc (cl-ton::tl-make "liteServer.getBlockHeader" :id (cl-ton::fc-sh-id b3) :mode 0)))))
             (check "verify-lookup-header: a lt lookup names the previous block" (and prev (= 4 (funcall seq-of (getf found :block-id)))))
             (check "...whose header closes it (verify-lookup-prev-header)"
                    (cl-ton:verify-lookup-prev-header prev-answer prev-id 2 :lt lt))
             (check "...and a predecessor that ends after lt does not"
                    (funcall refused (lambda () (cl-ton:verify-lookup-prev-header prev-answer prev-id 2
                                                                                  :lt (1- (cl-ton::fc-block-start-lt b3))))))
             (check "...nor the header of another block"
                    (funcall refused (lambda () (cl-ton:verify-lookup-prev-header al prev-id 2 :lt lt))))
             (check "...and a lt past the block's end is refused"
                    (funcall refused (lambda () (cl-ton:verify-lookup-header al 0 whole 2 :lt (+ 1000 (cl-ton::fc-block-end-lt b4)))))))
           ;; getShardBlockProof
           (let* ((id4 (cl-ton::fc-sh-id b4)) (ans (funcall shard-proof id4)))
             (check "verify-shard-block-proof: a shard block named by the masterchain block of its own seqno"
                    (let ((r (cl-ton:verify-shard-block-proof ans id4)))
                      (and (= 4 (funcall seq-of (getf r :mc-block))) (= 1 (getf r :links)))))
             (check "...a proof for another block is refused"
                    (funcall refused (lambda () (cl-ton:verify-shard-block-proof ans (cl-ton::fc-sh-id b3)))))
             (check "...as is a link proof of another block"
                    (funcall refused (lambda ()
                                       (cl-ton:verify-shard-block-proof
                                        (%obj-with ans :links (cl-ton::tl-get (funcall shard-proof (cl-ton::fc-sh-id b3)) :links))
                                        id4))))
             (check "...and a masterchain block is its own proof with no links"
                    (let ((r (cl-ton:verify-shard-block-proof (funcall shard-proof (cl-ton::fc-mc-id b3)) (cl-ton::fc-mc-id b3))))
                      (and (= 3 (funcall seq-of (getf r :mc-block))) (zerop (getf r :links)))))
             (progn
               (setf cl-ton::*fc-lookup-alt-seqno* 6)
               (unwind-protect
                    (check "...a chain of several shard blocks from a later masterchain block"
                           (let ((r (cl-ton:verify-shard-block-proof (funcall shard-proof (cl-ton::fc-sh-id b3)) (cl-ton::fc-sh-id b3))))
                             (and (= 6 (funcall seq-of (getf r :mc-block))) (= 4 (getf r :links)))))
                 (setf cl-ton::*fc-lookup-alt-seqno* nil))))
           ;; end to end over ADNL-ext against a liteserver that does not know lookupBlockWithProof
           (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                  (client (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc))))
             (setf cl-ton::*fc-lookup-with-proof-p* nil)
             (unwind-protect
                  (progn
                    (loop repeat 100 until (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl client)) do (sleep 0.1))
                    (let ((r3 (cl-ton:lite-lookup-block client 0 whole :seqno 3)))
                      (check "lite-lookup-block falls back: a shard block by seqno, placed in the chain by its masterchain block"
                             (and (= 3 (funcall seq-of (getf r3 :block-id))) (<= 3 (funcall seq-of (getf r3 :mc-block)))))
                      (check "...and the client remembers that lookupBlockWithProof is not known"
                             (not (cl-ton::lite-client-lookup-with-proof client))))
                    (check "...a masterchain block by seqno"
                           (= 2 (funcall seq-of (getf (cl-ton:lite-lookup-block client -1 whole :seqno 2) :block-id))))
                    (check "...a block by logical time"
                           (= 4 (funcall seq-of (getf (cl-ton:lite-lookup-block client 0 whole :lt (1+ (cl-ton::fc-block-start-lt b4)))
                                                      :block-id))))
                    (let* ((utime (cl-ton::fc-block-utime b4))
                           (want (cl-ton::fc-block-seqno (cl-ton::fc-lookup-pick fc 4 0 0 utime))))
                      (check "...a masterchain block by time"
                             (= want (funcall seq-of (getf (cl-ton:lite-lookup-block client -1 whole :utime utime) :block-id)))))
                    (check "...a block through a chain of several shard blocks"
                           (progn (setf cl-ton::*fc-lookup-alt-seqno* 6)
                                  (unwind-protect (= 3 (funcall seq-of (getf (cl-ton:lite-lookup-block client 0 whole :seqno 3) :block-id)))
                                    (setf cl-ton::*fc-lookup-alt-seqno* nil))))
                    (check "...a block that does not exist is a liteserver error"
                           (handler-case (progn (cl-ton:lite-lookup-block client 0 whole :seqno 9999) nil)
                             (cl-ton:lite-error () t))))
               (setf cl-ton::*fc-lookup-with-proof-p* t)
               (cl-ton:close-lite-client client))))))))

;;; --- shapes only a real liteserver showed ----------------------------------------------------

(defun test-verify-real-liteserver-shapes ()
  (format t "verify: back links with a pruned destination update, and a stale head~%")
  (if (not (%libs-available-p))
      (skip-missing "real liteserver shapes (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 10)
         (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                (open-client (lambda (&rest keys)
                               (let ((c (apply #'cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public
                                               (%zero-block-id fc) keys)))
                                 (loop repeat 100 until (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl c)) do (sleep 0.1))
                                 c))))
           ;; a backward link whose destination proof has a pruned state_update (what mainnet sends)
           (let ((client (funcall open-client)))
             (unwind-protect
                  (progn
                    (cl-ton:lite-sync client)
                    (setf cl-ton::*fc-prune-dest-update* t)
                    (check "lite-prove-block: an older masterchain block through a back link with a pruned destination update"
                           (progn (cl-ton:lite-prove-block client (cl-ton::fc-mc-id (cl-ton::fc-find-block fc 5))) t))
                    (check "...and a shard block through getShardBlockProof and such a back link"
                           (let ((cl-ton::*fc-lookup-with-proof-p* t))
                             (setf cl-ton::*fc-lookup-with-proof-p* nil)
                             (unwind-protect
                                  (= 4 (cl-ton::tl-get (getf (cl-ton:lite-lookup-block client 0 #x8000000000000000 :seqno 4) :block-id)
                                                       :seqno))
                               (setf cl-ton::*fc-lookup-with-proof-p* t)))))
               (setf cl-ton::*fc-prune-dest-update* nil)
               (cl-ton:close-lite-client client)))
           ;; a stale head: an upstream proves up to a head far behind the newest block
           (let ((client (funcall open-client :head-slack 2)))
             (unwind-protect
                  (progn
                    (check "head-slack: a head within the slack is accepted"
                           (<= 8 (cl-ton::tl-get (cl-ton:lite-sync client) :seqno)))
                    (setf cl-ton::*fc-proof-head-lag* 7)
                    (check "...a complete proof of a head 7 blocks behind is refused, the block the liteserver reported is asked for"
                           (<= (- (cl-ton::fc-head-seqno fc) 2) (cl-ton::tl-get (cl-ton:lite-sync client) :seqno)))
                    (setf cl-ton::*fc-proof-target-lag* 7)
                    (check "...and when even that answer lags, three tries end in a stale-head error"
                           (handler-case (progn (cl-ton:lite-sync client) nil)
                             (cl-ton::lite-stale-head () t))))
               (setf cl-ton::*fc-proof-head-lag* 0 cl-ton::*fc-proof-target-lag* 0)
               (cl-ton:close-lite-client client)))
           ;; without a slack nothing is checked
           (let ((client (funcall open-client)))
             (unwind-protect
                  (progn (setf cl-ton::*fc-proof-head-lag* 7)
                         (check "no head-slack: the old behaviour, any complete proof is taken"
                                (< (cl-ton::tl-get (cl-ton:lite-sync client) :seqno) (cl-ton::fc-head-seqno fc))))
               (setf cl-ton::*fc-proof-head-lag* 0)
               (cl-ton:close-lite-client client))))))))

;;; --- real links kept as vectors ----------------------------------------------------------------

(defun test-link-vectors ()
  (format t "verify: links cut out of a proof and kept as test vectors~%")
  (if (not (%libs-available-p))
      (skip-missing "link vectors (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 4)
         (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                (client (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc)))
                (seen '())
                (dir (format nil "/tmp/ton-trader-vectors-~D/" (sb-posix:getpid))))
           (unwind-protect
                (progn
                  (loop repeat 100 until (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl client)) do (sleep 0.1))
                  (let ((cl-ton:*lite-proof-hook* (lambda (proof) (push proof seen))))
                    (cl-ton:lite-sync client))
                  (check "the proof hook saw the proof the sync fetched" (= 1 (length seen)))
                  (let* ((proof (first seen))
                         (zero (cl-ton:proof-single-links proof :include-zero t)))
                    (check "proof-single-links: a link from the zero state only when asked" (and (= 1 (length zero)) (null (cl-ton:proof-single-links proof))))
                    (check "...each link is a proof of its own that verifies from its start block"
                           (let ((v (first zero)))
                             (= 1 (getf (cl-ton:verify-partial-block-proof (getf v :proof) (getf v :known)) :steps))))
                    (check "...an ordinary link, from seqno 0 to the head"
                           (let ((v (first zero))) (and (eq :ordinary (getf v :kind)) (= 0 (getf v :from-seqno)) (plusp (getf v :to-seqno)))))
                    (let* ((bin (cl-ton:save-link-vector (first zero) dir)))
                      (check "save-link-vector writes the .bin and the .sexp" (and (probe-file bin) (probe-file (make-pathname :type "sexp" :defaults bin))))
                      (multiple-value-bind (known loaded meta) (cl-ton:load-link-vector bin)
                        (check "load-link-vector gives back the start block, the proof and the description"
                               (and (cl-ton::%same-block-id-p known (getf (first zero) :known))
                                    (equalp (cl-ton::tl-encode loaded) (cl-ton::tl-encode (getf (first zero) :proof)))
                                    (eq :ordinary (getf meta :kind))))
                        (check "...and the loaded link verifies"
                               (= 1 (getf (cl-ton:verify-partial-block-proof loaded known) :steps))))
                      (%check-link-vector bin)
                      (check "a link that is not of the kind it says is not saved"
                             (handler-case (progn (cl-ton:save-link-vector (list* :kind :simplex (first zero)) dir) nil)
                               (error () t))))))
             (ignore-errors (uiop:delete-directory-tree (pathname dir) :validate t :if-does-not-exist :ignore))
             (cl-ton:close-lite-client client)))))))

;;; --- blockLinkBack ---------------------------------------------------------------------------

(defun test-verify-back-link ()
  (format t "verify: blockLinkBack (older targets), against the trusted block, and over ADNL-ext~%")
  (if (not (%libs-available-p))
      (skip-missing "back link verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 6)
         (let* ((known-blk (cl-ton::fc-find-block fc 5))
                (known (cl-ton::fc-mc-id known-blk))
                (b2 (cl-ton::fc-find-block fc 2)) (b3 (cl-ton::fc-find-block fc 3)) (b4 (cl-ton::fc-find-block fc 4))
                (zero-id (cl-ton::fc-zero-block-id fc))
                (ask (lambda (known target-id)
                       (cl-ton::tl-decode
                        (cl-ton::fc-answer-block-proof
                         fc (cl-ton::tl-make "liteServer.getBlockProof" :mode 1 :known-block known :target-block target-id)))))
                (to3 (cl-ton::fc-mc-id (cl-ton::fc-find-block fc 3)))
                (p3 (funcall ask known to3))
                (r3 (cl-ton:verify-partial-block-proof p3 known))
                (link3 (aref (cl-ton::tl-get p3 :steps) 0)))
           (check "a backward link from a non-key block (no state hash known) to an older block verifies"
                  (and (getf r3 :complete) (= 3 (cl-ton::tl-get (getf r3 :to) :seqno)) (= 1 (getf r3 :steps))
                       (equalp (getf r3 :state-hash) (cl-ton::node-hash (cl-ton::fc-block-mc-state b3)))))
           (check "...and its end is no key block"
                  (null (getf r3 :key-block)))
           (let* ((pz (funcall ask known zero-id)) (rz (cl-ton:verify-partial-block-proof pz known)))
             (check "a backward link to the zero state: no destination proof, its root hash is its state hash"
                    (and (getf rz :complete) (zerop (cl-ton::tl-get (getf rz :to) :seqno))
                         (equalp (getf rz :state-hash) (cl-ton::tl-get zero-id :root-hash))
                         (cl-ton::tl-get (aref (cl-ton::tl-get pz :steps) 0) :to-key-block))))
           (check "the target is the known block itself: an empty complete proof, nothing to verify (state hash not learned)"
                  (let* ((p (funcall ask known known)) (r (cl-ton:verify-partial-block-proof p known)))
                    (and (= 0 (length (cl-ton::tl-get p :steps))) (getf r :complete) (null (getf r :state-hash)))))
           (check "a chain of a backward link then forward links is walked in order (back to 3 then 3 -> 4 is refused: 3 is no key block)"
                  (%signals cl-ton:proof-error
                    (cl-ton:verify-partial-block-proof
                     (%obj-with p3 :to (cl-ton::fc-mc-id b4) :steps (vector link3 (cl-ton::fc-forward-link fc to3 b4))) known)))
           (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
             (refuses "a backward link checked against another trusted block"
                      (cl-ton:verify-partial-block-proof p3 (cl-ton::fc-mc-id b4)))
             (refuses "a proof from another block than the trusted one"
                      (cl-ton:verify-partial-block-proof (%obj-with p3 :from (cl-ton::fc-mc-id b4)) known))
             (refuses "a link that moves forward (the destination is newer)"
                      (cl-ton:verify-back-link (%obj-with link3 :to (cl-ton::fc-mc-id (cl-ton::fc-find-block fc 6))) known))
             (refuses "a destination the state does not list (a made-up block)"
                      (cl-ton:verify-back-link (%obj-with link3 :to (cl-ton::tl-block-id-ext :seqno 3 :root-hash (cl-ton::fc-block-sh-root b3)
                                                                                           :file-hash (cl-ton::fc-block-mc-file b3)))
                                               known))
             (refuses "another listed block's destination proof under this destination"
                      (cl-ton:verify-back-link (%obj-with link3 :dest-proof
                                                          (cl-ton::fc-proof-boc (cl-ton::fc-header-proof-node (cl-ton::fc-block-mc-block b2))))
                                               known))
             (refuses "the state proof of another block's state"
                      (cl-ton:verify-back-link (%obj-with link3 :state-proof
                                                          (cl-ton::fc-proof-boc (cl-ton::fc-prev-blocks-proof-node (cl-ton::fc-block-mc-state b4) 3)))
                                               known))
             (refuses "another block's source header proof"
                      (cl-ton:verify-back-link (%obj-with link3 :proof
                                                          (cl-ton::fc-proof-boc (cl-ton::fc-header-proof-node (cl-ton::fc-block-mc-block b4))))
                                               known))
             (refuses "a wrong to_key_block flag"
                      (cl-ton:verify-back-link (%obj-with link3 :to-key-block t) known))
             (refuses "no destination proof for a block that is not the zero state"
                      (cl-ton:verify-back-link (%obj-with link3 :dest-proof (make-array 0 :element-type '(unsigned-byte 8))) known))
             (refuses "a destination proof for the zero state"
                      (cl-ton:verify-back-link (%obj-with (aref (cl-ton::tl-get (funcall ask known zero-id) :steps) 0)
                                                          :dest-proof (cl-ton::tl-get link3 :dest-proof))
                                               known))
             (refuses "a forward link handed to the back-link checker"
                      (cl-ton:verify-back-link (cl-ton::fc-forward-link fc zero-id b2) zero-id)))
           (dolist (field '(:proof :state-proof :dest-proof))
             (let ((data (cl-ton::tl-get link3 field)) (accepted 0) (other 0))
               (dotimes (i 120)
                 (let ((bad (%flip-octet data (%vrnd (length data)) (ash 1 (%vrnd 8)))))
                   (handler-case (progn (cl-ton:verify-back-link (%obj-with link3 field bad) known) (incf accepted))
                     (cl-ton:proof-error () nil)
                     (error () (incf other)))))
               (check (format nil "120 single-bit corruptions of the link's ~(~A~): only ever a proof error, almost none verifies" field)
                      (and (zerop other) (< accepted 5)))))
           (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                  (client (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc))))
             (unwind-protect
                  (progn (loop repeat 100 until (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl client)) do (sleep 0.1))
                         (let ((head (cl-ton:lite-sync client)))
                           (check "lite-prove-block over ADNL-ext: an older block of the trusted chain, and the head itself"
                                  (and (= 3 (cl-ton::tl-get (getf (cl-ton:lite-prove-block client to3) :to) :seqno))
                                       (= (cl-ton::tl-get head :seqno)
                                          (cl-ton::tl-get (getf (cl-ton:lite-prove-block client head) :to) :seqno))))
                           (check "...and a block the chain does not have is refused or an error"
                                  (handler-case (progn (cl-ton:lite-prove-block
                                                        client (cl-ton::tl-block-id-ext :seqno 3 :root-hash (cl-ton::fc-block-sh-root b3)
                                                                                        :file-hash (cl-ton::fc-block-mc-file b3)))
                                                       nil)
                                    (cl-ton:ton-error () t)))))
               (cl-ton:close-lite-client client))))))))

;;; --- getLibrariesWithProof --------------------------------------------------------------------

(defun test-verify-libraries-with-proof ()
  (format t "verify: getLibrariesWithProof, against the masterchain state, and over ADNL-ext~%")
  (if (not (%libs-available-p))
      (skip-missing "libraries proof verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore proxy cfg))
         (cl-ton::fakechain-advance fc 2)
         (let* ((lib-a (cl-ton:end-cell (cl-ton:store-uint (cl-ton:begin-cell) 111111 32)))
                (lib-b (cl-ton:end-cell (cl-ton:store-ref (cl-ton:store-uint (cl-ton:begin-cell) 222222 32) lib-a)))
                (ha (cl-ton::hex->octets (cl-ton::fakechain-add-library fc lib-a)))
                (hb (cl-ton::hex->octets (cl-ton::fakechain-add-library fc lib-b))))
           (cl-ton::fakechain-advance fc 3)
           (let* ((head (cl-ton::fc-head fc)) (id (cl-ton::fc-mc-id head))
                  (old-id (cl-ton::fc-mc-id (cl-ton::fc-find-block fc 1)))
                  (unknown (cl-ton::sha256 (cl-ton::uint->octets 7 4)))
                  (ask (lambda (id hashes mode)
                         (cl-ton::tl-decode
                          (cl-ton::fc-answer-libraries-with-proof
                           fc (cl-ton::tl-make "liteServer.getLibrariesWithProof" :id id :mode mode
                                                                                   :library-list (coerce hashes 'vector))))))
                  (a (funcall ask id (list ha hb unknown) 1))
                  (r (cl-ton:verify-libraries-with-proof a id (list ha hb unknown) :mode 1)))
             (check "the published libraries are proved, served and hash to what was asked; an unpublished hash is absent"
                    (and (= 2 (length r)) (every (lambda (e) (equalp (cl-ton::node-hash-at (cdr e) 0) (car e))) r)
                         (not (assoc unknown r :test #'equalp))))
             (check "mode 3 (no data): the proof alone shows which are published"
                    (let ((x (cl-ton:verify-libraries-with-proof (funcall ask id (list ha hb) 3) id (list ha hb) :mode 3)))
                      (and (= 2 (length x)) (every (lambda (e) (null (cdr e))) x))))
             (check "a block from before the libraries were published: none, and that is proved too"
                    (null (cl-ton:verify-libraries-with-proof (funcall ask old-id (list ha hb) 1) old-id (list ha hb) :mode 1)))
             (check "only the first 16 hashes are answered: a library asked for as the 18th is neither served nor required"
                    (let ((many (append (loop for i below 17 collect (cl-ton::sha256 (cl-ton::uint->octets i 4))) (list ha))))
                      (null (cl-ton:verify-libraries-with-proof (funcall ask id many 1) id many :mode 1))))
             (let ((entries (coerce (cl-ton::tl-get a :result) 'list)))
               (flet ((with-result (list) (%obj-with a :result (coerce list 'vector))))
                 (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
                   (refuses "a published library left out"
                            (cl-ton:verify-libraries-with-proof (with-result (list (first entries))) id (list ha hb unknown) :mode 1))
                   (refuses "a library served that the proof shows is not published"
                            (cl-ton:verify-libraries-with-proof
                             (with-result (append entries (list (cl-ton::tl-make "liteServer.libraryEntry" :hash unknown
                                                                                  :data (cl-ton::serialize-boc lib-a)))))
                             id (list ha hb unknown) :mode 1))
                   (refuses "a library that was not asked for"
                            (cl-ton:verify-libraries-with-proof a id (list ha) :mode 1))
                   (refuses "the same library twice"
                            (cl-ton:verify-libraries-with-proof (with-result (append entries (list (first entries)))) id (list ha hb) :mode 1))
                   (refuses "the data of another library under this hash"
                            (cl-ton:verify-libraries-with-proof
                             (with-result (list (cl-ton::tl-make "liteServer.libraryEntry" :hash ha :data (cl-ton::serialize-boc lib-b))
                                                (second entries)))
                             id (list ha hb) :mode 1))
                   (refuses "garbage as library data"
                            (cl-ton:verify-libraries-with-proof
                             (with-result (list (cl-ton::tl-make "liteServer.libraryEntry" :hash ha :data (coerce (loop repeat 40 collect (%vrnd 256)) '(vector (unsigned-byte 8))))
                                                (second entries)))
                             id (list ha hb) :mode 1))
                   (refuses "data served although mode 2 asks for none"
                            (cl-ton:verify-libraries-with-proof (funcall ask id (list ha hb) 1) id (list ha hb) :mode 3))
                   (refuses "another mode than asked for"
                            (cl-ton:verify-libraries-with-proof (%obj-with a :mode 0) id (list ha hb unknown) :mode 1))
                   (refuses "an answer for another block"
                            (cl-ton:verify-libraries-with-proof a old-id (list ha hb unknown) :mode 1))
                   (refuses "the older block's proof with this block's entries"
                            (cl-ton:verify-libraries-with-proof
                             (%obj-with a :data-proof (cl-ton::tl-get (funcall ask old-id (list ha hb) 1) :data-proof)) id (list ha hb unknown) :mode 1))
                   (refuses "an empty data proof"
                            (cl-ton:verify-libraries-with-proof (%obj-with a :data-proof (make-array 0 :element-type '(unsigned-byte 8)))
                                                                id (list ha hb unknown) :mode 1))))
               (dolist (field '(:state-proof :data-proof))
                 (let ((data (cl-ton::tl-get a field)) (accepted 0) (other 0))
                   (dotimes (i 120)
                     (let ((bad (%flip-octet data (%vrnd (length data)) (ash 1 (%vrnd 8)))))
                       (handler-case (progn (cl-ton:verify-libraries-with-proof (%obj-with a field bad) id (list ha hb unknown) :mode 1)
                                            (incf accepted))
                         (cl-ton:proof-error () nil)
                         (error () (incf other)))))
                   (check (format nil "120 single-bit corruptions of the ~(~A~): only ever a proof error, almost none verifies" field)
                          (and (zerop other) (< accepted 5))))))
             (check "REAL tonlib (smc.getLibraries over the native proxy, which proof-checks getLibrariesWithProof itself) gets the same two libraries from this chain"
                    (let ((x (handler-case (progn (cl-ton::tonlib-sync tl) (cl-ton::tonlib-libraries tl (list ha unknown hb)))
                               (error (e) (format t "    tonlib: ~A~%" e) nil))))
                      (and (= 2 (length x))
                           (assoc (cl-ton::octets->hex ha) x :test #'string=)
                           (assoc (cl-ton::octets->hex hb) x :test #'string=))))
             (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                    (client (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc))))
               (unwind-protect
                    (progn (loop repeat 100 until (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl client)) do (sleep 0.1))
                           (check "lite-libraries over ADNL-ext: the two published libraries, not the unknown one"
                                  (let ((x (cl-ton:lite-libraries client (list ha unknown hb))))
                                    (and (= 2 (length x)) (assoc ha x :test #'equalp) (assoc hb x :test #'equalp)))))
                 (cl-ton:close-lite-client client)))))))))

;;; --- the mutation matrix (plan R2a) ------------------------------------------------------------
;;;
;;; For every verifier of a liteserver answer: change EVERY field of the answer, one at a time and
;;; (for nested objects and lists) every field of its parts, in the ways a lying server could -- flip a
;;; byte, empty it, cut it, swap in the same field of ANOTHER genuine answer, shift a number, drop or
;;; double a list entry -- and require that the verifier either refuses it with a proof error or (for a
;;; field the answer legitimately does not bind, listed per verifier) accepts the SAME verdict.  Any
;;; other outcome (a different result, another kind of error) is a gap.

(defun %mutate-octets (v donor)
  (let ((n (length v)) (out '()))
    (when (plusp n)
      (push (cons "first byte flipped" (%flip-octet v 0 1)) out)
      (push (cons "last byte flipped" (%flip-octet v (1- n) 128)) out)
      (push (cons "half cut" (subseq v 0 (floor n 2))) out))
    (push (cons "emptied" (make-array 0 :element-type '(unsigned-byte 8))) out)
    (when (and donor (not (equalp v donor))) (push (cons "another answer's" donor) out))
    out))

(defun %mutations (value donor)
  "A list of (LABEL . NEW-VALUE) for VALUE; DONOR is the same field of another genuine answer."
  (typecase value
    ((simple-array (unsigned-byte 8) (*)) (%mutate-octets value (and (typep donor '(simple-array (unsigned-byte 8) (*))) donor)))
    (integer (append (list (cons "+1" (1+ value)) (cons "-1" (1- value)) (cons "zero" 0))
                     (and (integerp donor) (/= donor value) (list (cons "another answer's" donor)))))
    (cl-ton::tl-obj
     (let ((out (and (typep donor 'cl-ton::tl-obj) (not (equalp donor value)) (list (cons "another answer's" donor)))))
       (loop for (k v) on (cl-ton::tl-obj-fields value) by #'cddr
             do (dolist (m (remove-if (lambda (m) (equalp (cdr m) v))
                                      (%mutations v (and (typep donor 'cl-ton::tl-obj) (getf (cl-ton::tl-obj-fields donor) k)))))
                  (push (cons (format nil "~(~A~): ~A" k (car m)) (%obj-with value k (cdr m))) out)))
       out))
    (vector
     (let* ((l (coerce value 'list)) (out '()))
       (when l
         (push (cons "first dropped" (coerce (rest l) 'vector)) out)
         (push (cons "first doubled" (coerce (cons (first l) l) 'vector)) out)
         (loop for i from 0 below (min 4 (length l))
               do (dolist (m (remove-if (lambda (m) (equalp (cdr m) (nth i l))) (%mutations (nth i l) nil)))
                    (push (cons (format nil "[~D] ~A" i (car m))
                                (coerce (append (subseq l 0 i) (list (cdr m)) (nthcdr (1+ i) l)) 'vector))
                          out))))
       out))
    (t (cond ((eq value t) (list (cons "negated" nil)))
             ((null value) (list (cons "negated" t)))
             (t nil)))))

(defun %run-matrix (name answer donor verify &key accepted-ok)
  "Mutate every field of ANSWER; return (VALUES ACCEPTED OTHER TOTAL): the labels of mutants the verifier
accepted with ACCEPTED-OK not covering them, and those that failed with an error that is not a proof error."
  (let ((accepted '()) (other '()) (total 0))
    (loop for (k v) on (cl-ton::tl-obj-fields answer) by #'cddr
          do (dolist (m (remove-if (lambda (m) (equalp (cdr m) v))
                                   (%mutations v (and donor (getf (cl-ton::tl-obj-fields donor) k))))
                      )
               (incf total)
               (let ((label (format nil "~A / ~(~A~): ~A" name k (car m))))
                 (handler-case (progn (funcall verify (%obj-with answer k (cdr m)))
                                      (unless (member k accepted-ok) (push label accepted)))
                   (cl-ton:proof-error () nil)
                   (error (e) (push (format nil "~A -> ~A: ~A" label (type-of e) e) other))))))
    (values (nreverse accepted) (nreverse other) total)))

(defun test-mutation-matrix ()
  (format t "verify: the mutation matrix over every liteserver answer verifier~%")
  (if (not (%libs-available-p))
      (skip-missing "mutation matrix (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 2)
         (let* ((lib (cl-ton:end-cell (cl-ton:store-uint (cl-ton:begin-cell) 424242 32)))
                (hl (cl-ton::hex->octets (cl-ton::fakechain-add-library fc lib))))
           (cl-ton::fakechain-advance fc 5)
           (let* ((head (cl-ton::fc-head fc)) (id (cl-ton::fc-mc-id head))
                  (b3 (cl-ton::fc-find-block fc 3)) (b4 (cl-ton::fc-find-block fc 4)) (b5 (cl-ton::fc-find-block fc 5))
                  (whole #x8000000000000000) (sw (- whole (expt 2 64)))
                  (known (cl-ton::fc-mc-id b5))
                  (zero-id (cl-ton::fc-zero-block-id fc))
                  (cases '()))
             (flet ((add (name answer donor verify &key accepted-ok)
                      (push (list name answer donor verify accepted-ok) cases))
                    (dec (octets) (cl-ton::tl-decode octets)))
               ;; getShardInfo
               (add "shardInfo" (dec (cl-ton::fc-answer-shard-info fc (cl-ton::tl-make "liteServer.getShardInfo" :id id :workchain 0 :shard sw :exact t)))
                    (dec (cl-ton::fc-answer-shard-info fc (cl-ton::tl-make "liteServer.getShardInfo" :id (cl-ton::fc-mc-id b4) :workchain 0 :shard sw :exact t)))
                    (lambda (a) (cl-ton:verify-shard-info a id 0 whole :exact t)))
               (add "shardInfo (none)" (dec (cl-ton::fc-answer-shard-info fc (cl-ton::tl-make "liteServer.getShardInfo" :id id :workchain 5 :shard sw :exact t)))
                    nil (lambda (a) (cl-ton:verify-shard-info a id 5 whole :exact t)))
               ;; lookupBlockWithProof: an older block (prev_blocks path), by lt (previous header), in the masterchain
               (flet ((lookup (wc mode &key (seqno 0) lt)
                        (dec (cl-ton::fc-answer-lookup-block
                              fc (apply #'cl-ton::tl-make "liteServer.lookupBlockWithProof" :mode mode
                                        :id (cl-ton::tl-make "tonNode.blockId" :workchain wc :shard sw :seqno seqno)
                                        :mc-block-id id (and lt (list :lt lt)))))))
                 (add "lookup seqno" (lookup 0 1 :seqno 3) (lookup 0 1 :seqno 4)
                      (lambda (a) (cl-ton:verify-lookup-block a id 0 whole 1 :seqno 3)) :accepted-ok '(:mode :prev-header))
                 (add "lookup masterchain" (lookup -1 1 :seqno 3) (lookup -1 1 :seqno 4)
                      (lambda (a) (cl-ton:verify-lookup-block a id -1 whole 1 :seqno 3)) :accepted-ok '(:mode :prev-header))
                 (let ((lt (1+ (cl-ton::fc-block-start-lt b4))))
                   (add "lookup lt" (lookup 0 2 :lt lt) (lookup 0 2 :lt (1+ (cl-ton::fc-block-start-lt b3)))
                        (lambda (a) (cl-ton:verify-lookup-block a id 0 whole 2 :lt lt)) :accepted-ok '(:mode))))
               ;; getBlockProof: a backward link, and the forward link from the zero state
               (let ((ask (lambda (kn target)
                            (dec (cl-ton::fc-answer-block-proof
                                  fc (cl-ton::tl-make "liteServer.getBlockProof" :mode 1 :known-block kn :target-block target))))))
                 (add "blockProof back" (funcall ask known (cl-ton::fc-mc-id b3)) (funcall ask known (cl-ton::fc-mc-id b4))
                      (lambda (a) (cl-ton:verify-partial-block-proof a known)) :accepted-ok '(:complete))
                 (add "blockProof forward" (funcall ask zero-id (cl-ton::fc-mc-id b3)) (funcall ask zero-id (cl-ton::fc-mc-id b4))
                      (lambda (a) (cl-ton:verify-partial-block-proof a zero-id :trusted-state-hash (cl-ton::tl-get zero-id :root-hash)))
                      :accepted-ok '(:complete)))
               ;; getLibrariesWithProof
               (flet ((libs (blk) (dec (cl-ton::fc-answer-libraries-with-proof
                                        fc (cl-ton::tl-make "liteServer.getLibrariesWithProof" :id (cl-ton::fc-mc-id blk) :mode 1
                                                                                                 :library-list (vector hl))))))
                 (add "libraries" (libs head) (libs b5)
                      (lambda (a) (cl-ton:verify-libraries-with-proof a id (list hl) :mode 1)))))
             (dolist (c (nreverse cases))
               (destructuring-bind (name answer donor verify accepted-ok) c
                 (check (format nil "~A: the genuine answer verifies" name) (progn (funcall verify answer) t))
                 (multiple-value-bind (accepted other total) (%run-matrix name answer donor verify :accepted-ok accepted-ok)
                   (dolist (a accepted) (format t "    ACCEPTED: ~A~%" a))
                   (dolist (o (subseq other 0 (min 8 (length other)))) (format t "    OTHER ERROR: ~A~%" o))
                   (check (format nil "~A: ~D field mutations, every one refused with a proof error" name total)
                          (and (null accepted) (null other))))))))))))

(defun test-mutation-matrix-2 ()
  (format t "verify: the mutation matrix over the older answer verifiers~%")
  (if (not (%libs-available-p))
      (skip-missing "mutation matrix, older verifiers (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (cl-ton:wallet-address w))
                (dest (fake-address #x66))
                (absent (fake-address #x77)))
           (dotimes (seqno 3)
             (%fc-enqueue fc (%transfer w seqno dest (cl-ton::nano 1/10)))
             (cl-ton::fakechain-advance fc 2))
           (let* ((blk (cl-ton::fc-head fc)) (id (cl-ton::fc-mc-id blk))
                  (prev (cl-ton::fc-find-block fc (1- (cl-ton::fc-block-seqno blk))))
                  (state (cl-ton:verify-account-state (%served-answer fc blk addr) addr id))
                  (lt (getf state :last-trans-lt)) (hash (getf state :last-trans-hash))
                  (cases '()))
             (flet ((add (name answer donor verify &key accepted-ok) (push (list name answer donor verify accepted-ok) cases))
                    (dec (octets) (cl-ton::tl-decode octets)))
               (add "accountState" (%served-answer fc blk addr) (%served-answer fc prev addr)
                    (lambda (a) (cl-ton:verify-account-state a addr id)))
               (add "accountState (absent)" (%served-answer fc blk absent) (%served-answer fc prev absent)
                    (lambda (a) (cl-ton:verify-account-state a absent id)))
               (add "transactions" (%tx-answer fc addr lt hash 20) (%tx-answer fc addr lt hash 2)
                    (lambda (a) (cl-ton:verify-transaction-list a addr lt hash :count 20))
                    ;; the block ids served beside the transactions are the server's claim, not proved
                    :accepted-ok '(:ids))
               (add "blockHeader" (dec (cl-ton::fc-answer-block-header fc (cl-ton::tl-make "liteServer.getBlockHeader" :id id :mode 0)))
                    (dec (cl-ton::fc-answer-block-header fc (cl-ton::tl-make "liteServer.getBlockHeader" :id (cl-ton::fc-mc-id prev) :mode 0)))
                    (lambda (a) (cl-ton:verify-block-header a id)) :accepted-ok '(:mode))
               (add "allShardsInfo" (dec (cl-ton::fc-answer-all-shards-info fc (cl-ton::tl-make "liteServer.getAllShardsInfo" :id id)))
                    (dec (cl-ton::fc-answer-all-shards-info fc (cl-ton::tl-make "liteServer.getAllShardsInfo" :id (cl-ton::fc-mc-id prev))))
                    (lambda (a) (cl-ton:verify-all-shards-info a id)))
               (add "configAll" (dec (cl-ton::fc-answer-config-all fc (cl-ton::tl-make "liteServer.getConfigAll" :mode 0 :id id)))
                    (dec (cl-ton::fc-answer-config-all fc (cl-ton::tl-make "liteServer.getConfigAll" :mode 0 :id (cl-ton::fc-mc-id prev))))
                    (lambda (a) (cl-ton:verify-config-info a id :all t :params '(34)))
                    :accepted-ok '(:mode)))
             (dolist (c (nreverse cases))
               (destructuring-bind (name answer donor verify accepted-ok) c
                 (check (format nil "~A: the genuine answer verifies" name) (progn (funcall verify answer) t))
                 (multiple-value-bind (accepted other total) (%run-matrix name answer donor verify :accepted-ok accepted-ok)
                   (dolist (a accepted) (format t "    ACCEPTED: ~A~%" a))
                   (dolist (o (subseq other 0 (min 8 (length other)))) (format t "    OTHER ERROR: ~A~%" o))
                   (check (format nil "~A: ~D field mutations, every one refused with a proof error" name total)
                          (and (null accepted) (null other))))))))))))
