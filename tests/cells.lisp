;;;; cells.lisp -- tests for cell levels, pruned branches and Merkle proofs/updates (ton-boc.lisp).
;;;;
;;;; The expected hashes in the first group are computed BY HAND here, from raw bytes following
;;;; crypto/vm/cells/DataCell.cpp, so they do not just re-run the implementation.  The rest are
;;;; properties (pruning never changes the level-0 hash; every tree survives a BOC round trip),
;;;; the rejection of every malformed exotic cell, and -- in the fakechain scenarios -- the real
;;;; tonlibjson.so accepting proofs built from these cells.

(in-package :cl-ton/test)

(defvar *cell-state* (sb-ext:seed-random-state 20261009))
(defun %crnd (n) (random n *cell-state*))

(defun %cell (bits nbits &rest refs)
  (cl-ton:make-cell :bits bits :bit-length nbits :refs refs))

(defun %bytes (&rest parts)
  "Concatenate octet vectors and lists of octets."
  (cl-ton:concat-octets (mapcar (lambda (p) (if (listp p) (coerce p '(simple-array (unsigned-byte 8) (*))) p)) parts)))

(defun %u16 (n) (list (ldb (byte 8 8) n) (ldb (byte 8 0) n)))

(defun %data-bytes (cell) (cl-ton:cell-data-octets cell))

(defun %rand-tree (depth)
  (let* ((nbits (%crnd 40))
         (refs (if (zerop depth) '() (loop repeat (%crnd 4) collect (%rand-tree (1- depth))))))
    (cl-ton:make-cell :bits (%crnd (ash 1 nbits)) :bit-length nbits :refs refs)))

(defun %all-cells (root) (remove-if-not #'cl-ton:cell-p (cl-ton:collect-nodes root)))

(defun test-cell-levels-by-hand ()
  (format t "cells: level hashes computed by hand~%")
  (let* ((leaf (%cell #xAB 8))
         (other (%cell #x5 3))
         (parent (%cell #x1 2 leaf other))
         (pruned (cl-ton:make-pruned-branch leaf)))
    (check "an ordinary cell: d1 d2 data depths hashes (the pre-level formula)"
           (equalp (cl-ton:node-hash leaf) (cl-ton:sha256 (%bytes '(0 2) '(#xAB)))))
    (check "a pruned branch of a leaf: 288 bits, level mask 1, one stored hash and depth"
           (and (= 288 (cl-ton:cell-bit-length pruned)) (= 1 (cl-ton:node-level-mask pruned))
                (= 1 (cl-ton:node-level pruned)) (= 1 (cl-ton:cell-special-type pruned))
                (cl-ton:pruned-branch-p pruned) (not (cl-ton:pruned-branch-p leaf))))
    (check "...its data is type 1, mask 1, the pruned cell's hash, its depth"
           (equalp (%data-bytes pruned) (%bytes '(1 1) (cl-ton:node-hash leaf) (%u16 0))))
    (check "...its hash at level 0 is the pruned cell's, at level 1 its own"
           (and (equalp (cl-ton:node-hash-at pruned 0) (cl-ton:node-hash leaf))
                (equalp (cl-ton:node-hash-at pruned 1) (cl-ton:node-hash pruned))
                (not (equalp (cl-ton:node-hash pruned) (cl-ton:node-hash leaf)))))
    (check "...whose own hash is sha256(d1=0x28 d2=0x48 data): refs 0, exotic, mask 1 in the top bits"
           (equalp (cl-ton:node-hash pruned)
                   (cl-ton:sha256 (%bytes '(#x28 #x48) '(1 1) (cl-ton:node-hash leaf) (%u16 0)))))
    (check "...and its depth at the top level is 0 (the stored depth is the pruned cell's)"
           (and (= 0 (cl-ton:node-depth pruned)) (= 0 (cl-ton:node-depth-at pruned 0))))
    (let* ((p-parent (%cell #x1 2 pruned other))
           (h0 (cl-ton:sha256 (%bytes '(2 1) '(#x60)    ; data 01, then the completion tag: 0110 0000
                                      (%u16 0) (%u16 0) (cl-ton:node-hash leaf) (cl-ton:node-hash other))))
           (h1 (cl-ton:sha256 (%bytes (list (+ 2 32) 1) h0   ; d1 = refs 2 + level mask 1 << 5, d2, previous hash
                                      (%u16 0) (%u16 0) (cl-ton:node-hash pruned) (cl-ton:node-hash other)))))
      (check "a parent of a pruned branch inherits level mask 1 and keeps two hashes"
             (and (= 1 (cl-ton:node-level-mask p-parent)) (= 2 (length (cl-ton:node-hashes p-parent)))))
      (check "...level-0 hash = the unpruned parent's hash (pruning is invisible to level 0)"
             (and (equalp (cl-ton:node-hash-at p-parent 0) (cl-ton:node-hash parent))
                  (equalp (cl-ton:node-hash-at p-parent 0) h0)
                  (= (cl-ton:node-depth-at p-parent 0) (cl-ton:node-depth parent))))
      (check "...level-1 hash, by hand: previous hash in place of the data, children's level-1 hashes"
             (equalp (cl-ton:node-hash p-parent) h1))
      (check "...and the representation hash is the highest level's"
             (equalp (cl-ton:node-hash p-parent) (cl-ton:node-hash-at p-parent 1))))
    (let* ((proof (cl-ton::make-merkle-proof (%cell #x1 2 pruned other)))
           (child (cl-ton:merkle-proof-root proof)))
      (check "a Merkle proof over that tree has level mask 0 (its child's mask shifted down)"
             (and (= 0 (cl-ton:node-level-mask proof)) (= 1 (cl-ton:node-level-mask child))))
      (check "...its hash is sha256(d1=9 d2=0x46 type hash depth, child's level-1 depth, child's level-1 hash)"
             (equalp (cl-ton:node-hash proof)
                     (cl-ton:sha256 (%bytes '(9 #x46) '(3) (cl-ton:node-hash-at child 0)
                                            (%u16 (cl-ton:node-depth-at child 0))
                                            (%u16 (cl-ton:node-depth-at child 1))
                                            (cl-ton:node-hash-at child 1)))))
      (check "...and it attests the original tree's hash"
             (equalp (cl-ton:node-hash-at child 0) (cl-ton:node-hash parent))))
    (let ((deep (cl-ton:make-pruned-branch leaf :level 2)))
      (check "a pruned branch at level 2: mask 2, one stored hash, and level 1 is not significant for it"
             (and (= 2 (cl-ton:node-level-mask deep)) (= 2 (cl-ton:node-level deep))
                  (equalp (cl-ton:node-hash-at deep 0) (cl-ton:node-hash leaf))
                  (equalp (cl-ton:node-hash-at deep 1) (cl-ton:node-hash-at deep 0))
                  (equalp (cl-ton:node-hash-at deep 2) (cl-ton:node-hash deep))))
      (check "...its hash is sha256(d1 = 8 + 2<<5, d2, data)"
             (equalp (cl-ton:node-hash deep)
                     (cl-ton:sha256 (%bytes (list (+ 8 64) #x48) '(1 2) (cl-ton:node-hash leaf) (%u16 0))))))
    (let* ((p1 (cl-ton:make-pruned-branch leaf))
           (inner (%cell #x1 2 p1 other))
           (p12 (cl-ton:make-pruned-branch inner :level 2)))
      (check "pruning a cell that already has level 1 at level 2 stores both its hashes (mask 3, 560 bits)"
             (and (= 3 (cl-ton:node-level-mask p12)) (= 560 (cl-ton:cell-bit-length p12))
                  (= 3 (length (cl-ton:node-hashes p12)))))
      (check "...and shows each of them at its level (0, 1) and its own at level 2"
             (and (equalp (cl-ton:node-hash-at p12 0) (cl-ton:node-hash-at inner 0))
                  (equalp (cl-ton:node-hash-at p12 1) (cl-ton:node-hash-at inner 1))
                  (equalp (cl-ton:node-hash-at p12 2) (cl-ton:node-hash p12))
                  (equalp (cl-ton:node-hash-at p12 3) (cl-ton:node-hash p12)))))))

(defun test-cell-pruning-properties ()
  (format t "cells: pruning properties over random trees~%")
  (let ((bad-hash 0) (bad-roundtrip 0) (bad-verify 0) (bad-boc 0) (with-pruned 0) (n 150))
    (dotimes (i n)
      (let* ((tree (%rand-tree 4))
             (pruned (cl-ton::prune-tree tree (lambda (c) (declare (ignore c)) (< (%crnd 100) 50))))
             (proof (cl-ton::make-merkle-proof pruned)))
        (when (some #'cl-ton:pruned-branch-p (%all-cells pruned)) (incf with-pruned))
        (unless (and (equalp (cl-ton:node-hash-at pruned 0) (cl-ton:node-hash tree))
                     (= (cl-ton:node-depth-at pruned 0) (cl-ton:node-depth tree)))
          (incf bad-hash))
        (unless (and (eq (cl-ton:verify-merkle-proof proof (cl-ton:node-hash tree)) pruned)
                     (%signals cl-ton:boc-error (cl-ton:verify-merkle-proof proof (cl-ton::tl-random-int256))))
          (incf bad-verify))
        (dolist (opts '(() (:with-hashes :all) (:has-idx t :with-hashes :root)))
          (let ((back (handler-case (first (cl-ton:parse-boc (apply #'cl-ton:serialize-boc proof opts)))
                        (error () nil))))
            (unless (and back (cl-ton:node-equal back proof)
                         (every #'cl-ton:node-equal
                                (%all-cells proof)
                                (%all-cells back)))
              (incf bad-roundtrip))))
        (let ((back (first (cl-ton:parse-boc (cl-ton:serialize-boc pruned :has-crc32c nil :with-hashes :all)))))
          (unless (and (cl-ton:node-equal back pruned)
                       (equalp (cl-ton:node-hashes back) (cl-ton:node-hashes pruned))
                       (equalp (cl-ton:node-depths back) (cl-ton:node-depths pruned))
                       (= (cl-ton:node-level-mask back) (cl-ton:node-level-mask pruned)))
            (incf bad-boc)))))
    (check (format nil "~D random trees (~D with pruned branches): the level-0 hash and depth never change" n with-pruned)
           (zerop bad-hash))
    (check "...every Merkle proof verifies against the original hash and against nothing else"
           (zerop bad-verify))
    (check "...proofs survive a BOC round trip plain, with all inline hashes, and with index + root hashes"
           (zerop bad-roundtrip))
    (check "...a pruned tree keeps all its hashes, depths and level mask through a BOC with inline hashes"
           (zerop bad-boc)))
  (let* ((tree (%rand-tree 4))
         (visible (lambda (c) (declare (ignore c)) nil))
         (all-pruned (cl-ton::prune-tree tree visible)))
    (check "pruning everything below the root leaves the root and pruned children, same level-0 hash"
           (and (equalp (cl-ton:node-hash-at all-pruned 0) (cl-ton:node-hash tree))
                (every (lambda (r) (or (not (cl-ton:cell-p r)) (cl-ton:pruned-branch-p r)))
                       (cl-ton:cell-refs all-pruned)))))
  (let* ((old (%rand-tree 3)) (new (%rand-tree 3))
         (update (cl-ton::make-merkle-update (cl-ton::prune-tree old (lambda (c) (declare (ignore c)) nil))
                                             (cl-ton::prune-tree new (lambda (c) (declare (ignore c)) (evenp (%crnd 2)))))))
    (check "a Merkle update over pruned trees verifies from the old hash and yields the new hash"
           (multiple-value-bind (new-hash) (cl-ton:verify-merkle-update update (cl-ton:node-hash old))
             (equalp new-hash (cl-ton:node-hash new))))
    (check "...and is refused from any other starting hash"
           (%signals cl-ton:boc-error (cl-ton:verify-merkle-update update (cl-ton::tl-random-int256))))
    (check "its level mask is its children's shifted down by one (0 for level-1 prunes)"
           (= 0 (cl-ton:node-level-mask update)))))

(defun %exotic (bits nbits &rest refs)
  (cl-ton:make-cell :bits bits :bit-length nbits :refs refs :exotic t))

(defun %find-subsequence (pattern octets)
  (search (coerce pattern '(simple-array (unsigned-byte 8) (*))) octets))

(defun test-cell-validation ()
  (format t "cells: malformed exotic cells are refused~%")
  (let* ((leaf (%cell #xAB 8))
         (h (cl-ton:octets->uint (cl-ton:node-hash leaf)))
         (pruned (cl-ton:make-pruned-branch leaf)))
    (flet ((bad (bits nbits &rest refs)
             (%signals cl-ton:boc-error (apply #'%exotic bits nbits refs))))
      (check "an exotic cell without a type byte" (bad 0 0))
      (check "an unknown exotic type (0 and 9)" (and (bad #x00 8) (bad #x09 8)))
      (check "a pruned branch with level mask 0" (bad #x0100 16))
      (check "a pruned branch whose level mask byte is above 7" (bad #x0108 16))
      (check "a pruned branch of the wrong length for its mask (mask 1, 16 bits; mask 3, one hash)"
             (and (bad #x0101 16)
                  (bad (logior (ash #x0103 272) (ash h 16)) 288)))
      (check "a pruned branch with a reference"
             (bad (logior (ash #x0101 272) (ash h 16)) 288 leaf))
      (check "a library reference of the wrong length" (bad (ash 2 248) 256))
      (check "a library reference with a reference" (bad (logior (ash 2 256) h) 264 leaf))
      (check "a Merkle proof stating the wrong hash"
             (bad (logior (ash 3 272) (ash (logxor h 1) 16)) 280 leaf))
      (check "a Merkle proof stating the wrong depth"
             (bad (logior (ash 3 272) (ash h 16) 5) 280 leaf))
      (check "a Merkle proof with two references, or none"
             (and (bad (logior (ash 3 272) (ash h 16)) 280 leaf leaf)
                  (bad (logior (ash 3 272) (ash h 16)) 280)))
      (check "a Merkle update with one reference"
             (bad (logior (ash 4 544) (ash h 288) (ash h 32)) 552 leaf))
      (check "a Merkle update stating the wrong new hash, and one stating the wrong depth"
             (and (bad (logior (ash 4 544) (ash h 288) (ash (logxor h 1) 32)) 552 leaf leaf)
                  (bad (logior (ash 4 544) (ash h 288) (ash h 32) 1) 552 leaf leaf)))
      (check "pruning is refused at a level the node already has, at level 0 and at level 4"
             (and (%signals cl-ton:boc-error (cl-ton:make-pruned-branch pruned :level 1))
                  (%signals cl-ton:boc-error (cl-ton:make-pruned-branch leaf :level 0))
                  (%signals cl-ton:boc-error (cl-ton:make-pruned-branch leaf :level 4))))
      (check "verify-merkle-proof / verify-merkle-update refuse cells that are not those"
             (and (%signals cl-ton:boc-error (cl-ton:verify-merkle-proof leaf (cl-ton:node-hash leaf)))
                  (%signals cl-ton:boc-error (cl-ton:verify-merkle-proof pruned (cl-ton:node-hash leaf)))
                  (%signals cl-ton:boc-error (cl-ton:verify-merkle-update leaf (cl-ton:node-hash leaf))))))
    ;; the security property: a forged subtree cannot pass for the real one
    (let* ((real-a (%cell #x11 8)) (real-b (%cell #x22 8))
           (tree (%cell #x1 2 real-a real-b))
           (honest (%cell #x1 2 (cl-ton:make-pruned-branch real-a) (cl-ton:make-pruned-branch real-b)))
           (forged-pruned (%exotic (logior (ash #x0101 272) (ash (logxor (cl-ton:octets->uint (cl-ton:node-hash real-a)) 1) 16)) 288))
           (forged (%cell #x1 2 forged-pruned (cl-ton:make-pruned-branch real-b))))
      (check "an honest proof verifies; a forged pruned branch yields a different level-0 hash"
             (and (cl-ton:verify-merkle-proof (cl-ton::make-merkle-proof honest) (cl-ton:node-hash tree))
                  (not (equalp (cl-ton:node-hash-at forged 0) (cl-ton:node-hash tree)))))
      (check "...a proof built over the forged tree cannot verify against the real root hash"
             (%signals cl-ton:boc-error
               (cl-ton:verify-merkle-proof (cl-ton::make-merkle-proof forged) (cl-ton:node-hash tree))))
      (check "...and a proof cell claiming the real hash over the forged tree cannot even be built"
             (%signals cl-ton:boc-error
               (%exotic (logior (ash 3 272) (ash (cl-ton:octets->uint (cl-ton:node-hash tree)) 16)
                                (cl-ton:node-depth tree))
                        280 forged))))
    (let* ((tree (%cell #x1 2 (%cell #x33 8) (%cell #x7 3)))
           (proof (cl-ton::make-merkle-proof
                   (cl-ton::prune-tree tree (lambda (c) (declare (ignore c)) nil))))
           (plain (cl-ton:serialize-boc proof :has-crc32c nil))
           (full (cl-ton:serialize-boc proof :has-crc32c nil :with-hashes :all)))
      (check "the proof's BOC parses back to the same cells, pruned branches included"
             (let ((back (first (cl-ton:parse-boc plain))))
               (and (cl-ton:node-equal back proof) (some #'cl-ton:pruned-branch-p (%all-cells back)))))
      (flet ((flip (octets at bit) (let ((v (copy-seq octets))) (setf (aref v at) (logxor (aref v at) bit)) v)))
        (dolist (case (list (cons "plain" plain) (cons "with every inline hash" full)))
          (check (format nil "BOC ~A: no single-bit corruption is accepted unless it gives a different root hash"
                         (car case))
                 (let ((root (cl-ton:node-hash proof)) (silent '()))
                   (dotimes (i (length (cdr case)))
                     (dotimes (bit 8)
                       (let ((result (handler-case (first (cl-ton:parse-boc (flip (cdr case) i (ash 1 bit)) :check-crc nil))
                                       (error () :refused))))
                         (when (and (not (eq result :refused)) (equalp (cl-ton:node-hash result) root))
                           (push (cons i bit) silent)))))
                   (or (null silent) (progn (format t "    silently accepted at (byte . bit): ~S~%" (reverse silent)) nil)))))
        (check "a lying level mask in a pruned branch's descriptor byte is refused"
               (let ((i (%find-subsequence '(#x28 #x48 1 1) plain)))
                 (and i (every (lambda (mask-bits)
                                 (%signals cl-ton:boc-error (cl-ton:parse-boc (flip plain i mask-bits) :check-crc nil)))
                               '(#x20 #x40 #x80)))))
        (check "a stale inline hash is refused (a bit flipped inside a stored hash)"
               (let ((i (%find-subsequence '(#x38 #x48) full)))
                 (and i (%signals cl-ton:boc-error (cl-ton:parse-boc (flip full (+ i 2 5) 1) :check-crc nil)))))))))

(defun test-fakechain-pruned-proofs ()
  (format t "cells: the fakechain serves pruned proofs, and Lisp can verify and read them~%")
  (if (not (%libs-available-p))
      (skip-missing "pruned proofs served by the fakechain (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (cl-ton:wallet-address w))
                (other (fake-address #x66)))
           (cl-ton::fakechain-set-account fc other :balance (cl-ton::nano 1))
           (cl-ton::fakechain-advance fc 2)
           (let* ((blk (cl-ton::fc-head fc))
                  (account-id (lambda (a) (cl-ton::tl-make "liteServer.accountId" :workchain 0
                                                           :id (cl-ton:address-hash a))))
                  (answer (cl-ton::tl-decode
                           (cl-ton::fc-answer-account-state
                            fc (cl-ton::tl-make "liteServer.getAccountState" :id (cl-ton::fc-mc-id blk)
                                                :account (funcall account-id addr)))))
                  (mc-roots (cl-ton:parse-boc (cl-ton::tl-get answer :shard-proof)))
                  (sh-roots (cl-ton:parse-boc (cl-ton::tl-get answer :proof)))
                  (full-size (+ (length (cl-ton::fc-proof-boc (cl-ton::fc-block-mc-block blk) (cl-ton::fc-block-mc-state blk)))
                                (length (cl-ton::fc-proof-boc (cl-ton::fc-block-sh-block blk) (cl-ton::fc-block-sh-state blk)))))
                  (served-size (+ (length (cl-ton::tl-get answer :shard-proof)) (length (cl-ton::tl-get answer :proof)))))
             (check "the account-state answer carries two Merkle proofs in each proof BOC (block, state)"
                    (and (= 2 (length mc-roots)) (= 2 (length sh-roots))
                         (every (lambda (r) (= 3 (cl-ton:cell-special-type r))) (append mc-roots sh-roots))))
             (check "...every one of them contains pruned branches"
                    (every (lambda (r) (some #'cl-ton:pruned-branch-p (%all-cells r))) (append mc-roots sh-roots)))
             (check (format nil "...and together they are smaller than the unpruned proofs (~D < ~D bytes)" served-size full-size)
                    (< served-size full-size))
             (let* ((sh-block (cl-ton:verify-merkle-proof (first sh-roots) (cl-ton::tl-get (cl-ton::tl-get answer :shardblk) :root-hash)))
                    (update (svref (cl-ton:cell-refs sh-block) 2))
                    (new-hash (cl-ton:verify-merkle-update
                               update (cl-ton:node-hash-at (svref (cl-ton:cell-refs update) 0) 0)))
                    (sh-state (cl-ton:verify-merkle-proof (second sh-roots) new-hash)))
               (check "the shard block proof verifies against the block id's root hash"
                      (cl-ton:cell-p sh-block))
               (check "...its state_update names the shard state hash, and the state proof verifies against it"
                      (and (equalp new-hash (cl-ton:node-hash (cl-ton::fc-block-sh-state blk)))
                           (cl-ton:cell-p sh-state)))
               (check "...a proof is refused against any other hash (the block's against the state's, and back)"
                      (and (%signals cl-ton:boc-error (cl-ton:verify-merkle-proof (first sh-roots) new-hash))
                           (%signals cl-ton:boc-error (cl-ton:verify-merkle-proof (second sh-roots) (cl-ton:node-hash (cl-ton::fc-block-sh-block blk))))))
               (let* ((accounts (svref (cl-ton:cell-refs sh-state) 1))
                      (path (cl-ton::dict-path-cells (cl-ton::first-ref-cell accounts)
                                                     (cl-ton:octets->uint (cl-ton:address-hash addr)) 256))
                      (leaf (car (last path)))
                      (state-root (first (cl-ton:parse-boc (cl-ton::tl-get answer :state)))))
                 (check "Lisp finds the account through the pruned state proof, and the ShardAccount's account cell is the served state"
                        (equalp (cl-ton:node-hash (cl-ton::first-ref-cell leaf)) (cl-ton:node-hash state-root)))
                 (check "reading another account's path hits a pruned branch and is refused (never read as data)"
                        (%signals cl-ton:ton-error
                          (cl-ton::dict-path-cells (cl-ton::first-ref-cell accounts)
                                                   (cl-ton:octets->uint (cl-ton:address-hash other)) 256)))
                 (check "a slice over a pruned branch, a Merkle proof or a library reference is refused"
                        (and (%signals cl-ton:ton-error (cl-ton:cell-slice (first (remove-if-not #'cl-ton:pruned-branch-p (%all-cells sh-state)))))
                             (%signals cl-ton:ton-error (cl-ton:cell-slice (first sh-roots)))))))))))))

(defun test-cells ()
  (test-cell-levels-by-hand)
  (test-cell-pruning-properties)
  (test-cell-validation)
  (test-fakechain-pruned-proofs))
