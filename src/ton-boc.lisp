;;;; ton-boc.lisp
;;;;
;;;; A Cell / BOC (Bag of Cells) serializer and parser for the TON
;;;; blockchain, written in Common Lisp (SBCL), using ironclad for
;;;; SHA-256 and SB-THREAD for parallelism.
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

;;;; Load with:
;;;;   (asdf:load-system :cl-ton)
;;;;   (cl-ton:run-boc-tests)
;;;;   (cl-ton:demo)
;;;;
;;;; Design
;;;;   Everything is a value.  BUILDERs and CELLs are immutable structs with
;;;;   read-only slots: every STORE-* operation returns a new builder, and
;;;;   END-CELL / MAKE-CELL compute the representation hash, depth and level
;;;;   exactly once, at construction time.  There are no caches to
;;;;   invalidate, no "finished" flag, and cells can be shared between
;;;;   threads without any synchronization.  The only mutation left is local
;;;;   to a handful of functions - filling a freshly allocated vector, or a
;;;;   visited-set hash table that never escapes - so every exported function
;;;;   is referentially transparent.
;;;;
;;;;   SERIALIZE-BOC serializes cell bodies in parallel with SB-THREAD (see
;;;;   PMAP, *WORKER-COUNT* and *PARALLEL-THRESHOLD*).  PMAP is exported so
;;;;   that callers can build independent subtrees in parallel as well.
;;;;
;;;; Implements
;;;;   - ordinary cells (<= 1023 bits, <= 4 refs) and their standard
;;;;     representation hash, per
;;;;     https://docs.ton.org/foundations/serialization/cells
;;;;   - content-hash deduplication: structurally identical subtrees built as
;;;;     separate objects are merged into one BOC cell (the tree becomes a DAG)
;;;;   - absent cells: external references known only by hash and depth,
;;;;     counted in the header's `absent' field
;;;;   - hash-inlined cells (h = 1 in d1): none, roots only, all, or by
;;;;     predicate
;;;;   - optional index, optional CRC32C, multiple roots, per
;;;;     https://docs.ton.org/foundations/serialization/boc
;;;;   - PARSE-BOC, the inverse, which verifies inlined hashes and the CRC32C
;;;;
;;;; Levels (crypto/vm/cells/DataCell.cpp)
;;;;   A cell has a level MASK (3 bits): bit i-1 set means the cell has a hash of its own at
;;;;   level i.  Ordinary cells inherit the OR of their children's masks; exotic cells (the
;;;;   first data byte is the type) follow their type: pruned branch (1) states its mask, library
;;;;   reference (2) has none, Merkle proof (3) and Merkle update (4) shift their children's mask
;;;;   down by one.  A cell carries one hash and depth per significant level (level 0 always), the
;;;;   highest being its representation hash; a parent hashes its children at its own level, one
;;;;   higher under a Merkle proof/update.  Exotic cells are validated as the C++ does.
;;;;
;;;; Not implemented
;;;;   - has_cache_bits.
;;;;
;;;; Wire format (cross-checked against ton-blockchain/ton, crypto/vm/boc.cpp
;;;; and crypto/vm/cells/DataCell.cpp, and against @ton/core):
;;;;   ordinary cell body = d1 d2 [hash(32) depth(2)]{h=1} data ref-index{r}
;;;;   absent cell body   = d1 d2 hash(32) depth(2)
;;;;                        with d1 = 7 + 16 (+ 8 if exotic): r = 7 forces h = 1
;;;;   d1 = r + 8*exotic + 16*h + 32*level, d2 = floor(b/8) + ceil(b/8).
;;;;   Note that the C++ reference deserializer currently rejects absent
;;;;   cells ("TODO: absent cells"), so BOCs containing them round-trip
;;;;   through PARSE-BOC here but are not accepted by the node.
;;;;
;;;; Part of :CL-TON (see src/package.lisp for the full export list); no
;;;; longer its own :TON-BOC package -- nothing here needs less than the
;;;; rest of the client, and everything here needs to be visible to it.

(in-package :cl-ton)

;;; ---------------------------------------------------------------------
;;; Conditions
;;; ---------------------------------------------------------------------

(define-condition boc-error (simple-error) ()
  (:documentation "Signalled for invalid cells, invalid BOCs and limit violations."))

(defun boc-error (format-control &rest format-arguments)
  (error 'boc-error :format-control format-control :format-arguments format-arguments))

;;; ---------------------------------------------------------------------
;;; Octet vectors: small pure helpers
;;; ---------------------------------------------------------------------

(deftype octets () '(simple-array (unsigned-byte 8) (*)))

(defun octets (&rest bytes)
  (make-array (length bytes) :element-type '(unsigned-byte 8) :initial-contents bytes))

(defun as-octets (sequence)
  (if (typep sequence 'octets) sequence (coerce sequence 'octets)))

(defun concat-octets (sequences)
  "Concatenate a list of octet sequences into one fresh OCTETS vector."
  (let ((out (make-array (reduce #'+ sequences :key #'length)
                         :element-type '(unsigned-byte 8))))
    (loop for seq in sequences
          for start = 0 then end
          for end = (+ start (length seq))
          do (replace out seq :start1 start))
    out))

(defun uint->octets (value nbytes)
  "Big-endian encoding of the non-negative integer VALUE in NBYTES bytes."
  (let ((out (make-array nbytes :element-type '(unsigned-byte 8))))
    (loop for i from 0 below nbytes
          do (setf (aref out i) (ldb (byte 8 (* 8 (- nbytes 1 i))) value)))
    out))

(defun octets->uint (octets &key (start 0) (end (length octets)))
  "The big-endian unsigned integer of OCTETS[START, END).  Whole 64-bit words are gathered without
boxing, so a 32-octet hash costs one or two bignums instead of one per octet."
  (if (typep octets '(simple-array (unsigned-byte 8) (*)))
      (let ((acc 0) (i start))
        (declare (type unsigned-byte acc) (type fixnum i start end)
                 (type (simple-array (unsigned-byte 8) (*)) octets))
        (loop while (<= (+ i 8) end)
              do (let ((w 0))
                   (declare (type (unsigned-byte 64) w))
                   (dotimes (k 8)
                     (setf w (logior (ldb (byte 64 0) (ash w 8)) (aref octets (+ i k)))))
                   (setf acc (logior (ash acc 64) w)))
                 (incf i 8))
        (loop while (< i end)
              do (setf acc (logior (ash acc 8) (aref octets i)))
                 (incf i))
        acc)
      (reduce (lambda (acc b) (logior (ash acc 8) b)) octets
              :start start :end end :initial-value 0)))

(defun bytes-needed (n)
  "Smallest number of bytes (at least 1) whose big-endian encoding holds N."
  (max 1 (ceiling (integer-length n) 8)))

(defun octets->hex (octets)
  (format nil "~(~{~2,'0x~}~)" (coerce octets 'list)))

(defun hex->octets (string)
  (let ((hex (remove-if (lambda (c) (member c '(#\Space #\Newline #\Tab))) string)))
    (unless (evenp (length hex))
      (boc-error "Hex string has odd length: ~S" string))
    (if (zerop (length hex))
        (octets)
        (uint->octets (parse-integer hex :radix 16) (/ (length hex) 2)))))

(defun sha256 (octets)
  (ironclad:digest-sequence :sha256 octets))

;;; ---------------------------------------------------------------------
;;; Threads
;;; ---------------------------------------------------------------------

(defun cpu-count ()
  "Number of online CPUs, or 1 if it cannot be determined."
  (let ((n #+sbcl (ignore-errors
                   (sb-alien:alien-funcall
                    (sb-alien:extern-alien "sysconf" (function sb-alien:long sb-alien:int))
                    ;; _SC_NPROCESSORS_ONLN
                    #+linux 84 #+darwin 58 #-(or linux darwin) -1))
           #-sbcl nil))
    (if (and (integerp n) (plusp n)) n 1)))

(defparameter *worker-count* (cpu-count)
  "Default number of SB-THREAD threads used by PMAP.")

(defparameter *parallel-threshold* 64
  "SERIALIZE-BOC serializes cell bodies with PMAP only for BOCs with at
least this many cells; smaller ones are not worth the thread start-up.")

(defun split-list (list parts)
  "Split LIST into at most PARTS consecutive chunks of (nearly) equal size."
  (if (null list)
      '()
      (let ((size (ceiling (length list) parts)))
        (loop for tail on list by (lambda (l) (nthcdr size l))
              collect (loop for x in tail repeat size collect x)))))

(defvar *pmap-conveyed* '()
  "Special variables whose CURRENT values PMAP hands to its worker threads.  A new SBCL thread sees the global value of
a special, not the binding of the thread that made it, so a dynamically bound setting (the block the getters are pinned
to, the trial's getter log) would silently not apply inside a worker without this.  Files that define such a variable
PUSHNEW it here.")

(defun pmap (function list &key (threads *worker-count*))
  "MAPCAR FUNCTION over LIST using up to THREADS SB-THREAD threads; the
result has the same order as LIST.  FUNCTION must be thread-safe, which is
trivially the case for pure functions over immutable cells.  An error
signalled inside a worker is re-signalled in the calling thread, after ALL workers
have finished."
  (let ((parts (min threads (length list))))
    (if (< parts 2)
        (mapcar function list)
        #-sb-thread (mapcar function list)
        #+sb-thread
        (let* ((vars (remove-if-not #'boundp *pmap-conveyed*))
               (vals (mapcar #'symbol-value vars))
               (workers
                 (mapcar (lambda (chunk)
                           (sb-thread:make-thread
                            (lambda ()
                              (progv vars vals
                                (handler-case (cons :ok (mapcar function chunk))
                                  (error (e) (cons :error e)))))
                            :name "ton-boc pmap worker"))
                         (split-list list parts))))
          ;; Join EVERY worker before signalling anything: re-signalling the first error
          ;; straight away lets the caller unwind (and tear down whatever the other workers
          ;; are still using -- e.g. close a tonlib client mid-request) under their feet.
          (let ((results (mapcar #'sb-thread:join-thread workers)))
            (let ((failed (find :error results :key #'car)))
              (when failed (error (cdr failed))))
            (loop for (nil . payload) in results append payload))))))

;;; ---------------------------------------------------------------------
;;; Descriptor bytes and data layout shared by hashing and serialization
;;; ---------------------------------------------------------------------

(defun d1-byte (refs-count exotic-p level-mask &key with-hashes)
  (+ refs-count (if exotic-p 8 0) (if with-hashes 16 0) (* 32 level-mask)))

(defun d2-byte (bit-length)
  (+ (floor bit-length 8) (ceiling bit-length 8)))

(defun data-octets (bits bit-length)
  "The data bits as ceil(BIT-LENGTH/8) bytes.  When BIT-LENGTH is not a
multiple of 8 a completion tag (a 1 followed by zeros) fills the last byte."
  (let ((rem (mod bit-length 8)))
    (uint->octets (if (zerop rem)
                      bits
                      (ash (logior (ash bits 1) 1) (- 7 rem)))
                  (ceiling bit-length 8))))

;;; ---------------------------------------------------------------------
;;; Cells
;;;
;;; NODE is anything a cell can reference: a CELL whose contents are known,
;;; or an ABSENT-CELL known only by hash and depth.  Both are immutable.
;;; ---------------------------------------------------------------------

(defstruct (node (:constructor nil) (:copier nil) (:predicate node-p))
  (hash (octets) :type octets :read-only t)        ; the representation hash: the highest level's
  (depth 0 :type (unsigned-byte 16) :read-only t)  ; ... and its depth
  (level 0 :type (integer 0 3) :read-only t)       ; the highest significant level
  (level-mask 0 :type (integer 0 7) :read-only t)  ; bit i-1: a hash of its own at level i
  (hashes #() :type simple-vector :read-only t)    ; one per significant level, lowest first
  (depths #() :type simple-vector :read-only t))

(defstruct (cell (:include node)
                 (:constructor %make-cell (hash depth level level-mask hashes depths
                                           bits bit-length refs exotic-p))
                 (:copier nil)
                 (:predicate cell-p))
  (bits 0 :type unsigned-byte :read-only t)              ; data, MSB first
  (bit-length 0 :type (integer 0 1023) :read-only t)
  (refs #() :type simple-vector :read-only t)            ; of NODE, <= 4
  (exotic-p nil :type boolean :read-only t))

(defstruct (absent-cell (:include node)
                        (:constructor %make-absent-cell (hash depth level level-mask hashes depths))
                        (:copier nil)
                        (:predicate absent-cell-p)))

(defun node-hash-hex (node)
  (octets->hex (node-hash node)))

(defun hash-key (node)
  "The representation hash as an integer: an EQL-hashable identity."
  (octets->uint (node-hash node)))

(defun node-equal (a b)
  "Two nodes are the same cell iff their representation hashes agree."
  (equalp (node-hash a) (node-hash b)))

(defmethod print-object ((c cell) stream)
  (print-unreadable-object (c stream :type t)
    (format stream "~D bit~:P, ~D ref~:P, ~A.." (cell-bit-length c) (length (cell-refs c))
            (subseq (node-hash-hex c) 0 16))))

(defmethod print-object ((c absent-cell) stream)
  (print-unreadable-object (c stream :type t)
    (format stream "depth ~D, ~A.." (node-depth c) (subseq (node-hash-hex c) 0 16))))

;;; --- levels ---------------------------------------------------------------

(defun level-hash-index (level-mask level)
  "The index into a cell's hashes/depths vectors of its hash at LEVEL (level_mask.apply(level)
.get_hash_i()): how many significant levels lie below LEVEL."
  (logcount (ldb (byte level 0) level-mask)))

(defun node-hash-at (node level)
  "NODE's hash as seen at LEVEL (0..3, a Merkle proof's children are read one higher)."
  (svref (node-hashes node) (level-hash-index (node-level-mask node) level)))

(defun node-depth-at (node level)
  (svref (node-depths node) (level-hash-index (node-level-mask node) level)))

(defun %field (bits bit-length start width)
  "The WIDTH bits of cell data BITS (BIT-LENGTH bits, most significant first) from bit START."
  (ldb (byte width (- bit-length start width)) bits))

(defun %field-octets (bits bit-length start width-bytes)
  (uint->octets (%field bits bit-length start (* 8 width-bytes)) width-bytes))

(defun %special-type (exotic-p bits bit-length)
  (cond ((not exotic-p) 0)
        ((< bit-length 8) (boc-error "An exotic cell has a type byte, but this one has ~D bits" bit-length))
        (t (%field bits bit-length 0 8))))

(defmacro %need (test control &rest arguments)
  "Signal a BOC-ERROR unless TEST: the checks of an exotic cell's layout read as a list of facts."
  `(unless ,test (boc-error ,control ,@arguments)))

(defun %validate-exotic (type bits bit-length refs)
  "Check an exotic cell of TYPE as DataCell.cpp does; (VALUES LEVEL-MASK STORED-HASHES STORED-DEPTHS),
the stored lists only for a pruned branch."
  (let ((nrefs (length refs)))
    (case type
      (1                                ; pruned branch: type, level mask, hashes, depths
       (%need (and (zerop nrefs) (>= bit-length 16)) "A pruned branch has no references and a level mask byte")
       (let* ((mask (%field bits bit-length 8 8)) (k (logcount mask)))
         (%need (<= 1 mask 7) "A pruned branch's level mask must be 1..7, got ~D" mask)
         (%need (= bit-length (* 8 (+ 2 (* 34 k))))
                "A pruned branch of level mask ~D has ~D bits, expected ~D" mask bit-length (* 8 (+ 2 (* 34 k))))
         (values mask
                 (loop for j below k collect (%field-octets bits bit-length (+ 16 (* 256 j)) 32))
                 (loop for j below k collect (%field bits bit-length (+ 16 (* 256 k) (* 16 j)) 16)))))
      (2                                ; library reference: type, hash
       (%need (and (= bit-length 264) (zerop nrefs)) "A library reference is 264 bits and has no references")
       (values 0 nil nil))
      (3                                ; Merkle proof: type, hash, depth; one child
       (%need (and (= bit-length 280) (= nrefs 1)) "A Merkle proof is 280 bits with one reference")
       (let ((child (svref refs 0)))
         (%need (equalp (%field-octets bits bit-length 8 32) (node-hash-at child 0))
                "A Merkle proof's hash does not match its subtree")
         (%need (= (%field bits bit-length 264 16) (node-depth-at child 0))
                "A Merkle proof's depth does not match its subtree")
         (values (ash (node-level-mask child) -1) nil nil)))
      (4                                ; Merkle update: type, two hashes, two depths; two children
       (%need (and (= bit-length 552) (= nrefs 2)) "A Merkle update is 552 bits with two references")
       (let ((old (svref refs 0)) (new (svref refs 1)))
         (%need (and (equalp (%field-octets bits bit-length 8 32) (node-hash-at old 0))
                     (equalp (%field-octets bits bit-length 264 32) (node-hash-at new 0)))
                "A Merkle update's hashes do not match its subtrees")
         (%need (and (= (%field bits bit-length 520 16) (node-depth-at old 0))
                     (= (%field bits bit-length 536 16) (node-depth-at new 0)))
                "A Merkle update's depths do not match its subtrees")
         (values (ash (logior (node-level-mask old) (node-level-mask new)) -1) nil nil)))
      (t (boc-error "Unknown exotic cell type ~D" type)))))

(defun %compute-levels (type mask exotic-p bits bit-length refs stored-hashes stored-depths)
  "(VALUES HASHES DEPTHS), one entry per significant level of MASK, lowest first.  Each hash is the
SHA-256 of d1 (with the mask below that level), d2, then the cell's data for the first hash or the
previous hash for the others, then the children's depths and hashes at that level (one higher
under a Merkle proof/update).  A pruned branch computes only its highest hash: the lower ones
are the ones it stores."
  (let* ((total (1+ (logcount mask)))
         (offset (if (= type 1) (1- total) 0))
         (merkle (if (member type '(3 4)) 1 0))
         (hashes (make-array total)) (depths (make-array total)) (i 0))
    (loop for level from 0 to 3
          when (or (zerop level) (logbitp (1- level) mask))
            do (if (< i offset)
                   (setf (svref hashes i) (as-octets (pop stored-hashes))
                         (svref depths i) (pop stored-depths))
                   (let* ((child-level (+ level merkle))
                          (d1 (d1-byte (length refs) exotic-p (ldb (byte level 0) mask))))
                     (setf (svref hashes i)
                           (sha256 (concat-octets
                                    (list* (octets d1 (d2-byte bit-length))
                                           (if (= i offset) (data-octets bits bit-length) (svref hashes (1- i)))
                                           (append (map 'list (lambda (r) (uint->octets (node-depth-at r child-level) 2)) refs)
                                                   (map 'list (lambda (r) (node-hash-at r child-level)) refs)))))
                           (svref depths i)
                           (if (zerop (length refs))
                               0
                               (1+ (reduce #'max refs :key (lambda (r) (node-depth-at r child-level))))))
                     (unless (< (svref depths i) 65536)
                       (boc-error "Cell depth ~D exceeds 65535" (svref depths i)))))
               (incf i))
    (values hashes depths)))

(defun make-cell (&key (bits 0) (bit-length 0) (refs '()) exotic)
  "Construct an immutable cell.  BITS is the data as a non-negative integer of BIT-LENGTH bits
(most significant bit first); REFS is a sequence of at most four NODEs.  The level mask, the
hashes and the depths are computed here, once, from the (already built) children; an exotic cell
is validated as DataCell.cpp does."
  (let ((refs (coerce refs 'simple-vector)))
    (unless (and (integerp bit-length) (<= 0 bit-length 1023))
      (boc-error "Cell data must be 0..1023 bits, got ~A" bit-length))
    (unless (and (integerp bits) (<= 0 bits) (< bits (ash 1 bit-length)))
      (boc-error "Data ~A does not fit in ~D bits" bits bit-length))
    (unless (<= (length refs) 4)
      (boc-error "A cell may have at most 4 references, got ~D" (length refs)))
    (unless (every #'node-p refs)
      (boc-error "References must be cells or absent cells: ~S" refs))
    (let* ((exotic-p (and exotic t))
           (type (%special-type exotic-p bits bit-length)))
      (multiple-value-bind (mask stored-hashes stored-depths)
          (if exotic-p
              (%validate-exotic type bits bit-length refs)
              (values (reduce #'logior refs :key #'node-level-mask :initial-value 0) nil nil))
        (multiple-value-bind (hashes depths)
            (%compute-levels type mask exotic-p bits bit-length refs stored-hashes stored-depths)
          (%make-cell (svref hashes (1- (length hashes))) (svref depths (1- (length depths)))
                      (integer-length mask) mask hashes depths bits bit-length refs exotic-p))))))

(defun make-absent-cell (hash &key (depth 0))
  "A reference to a cell that is not part of the BOC and is known only by its 32-byte
representation HASH (octets or hex string) and its DEPTH; it has level mask 0."
  (let ((hash (if (stringp hash) (hex->octets hash) (as-octets hash))))
    (unless (= (length hash) 32)
      (boc-error "A cell hash has 32 bytes, got ~D" (length hash)))
    (unless (and (integerp depth) (<= 0 depth 65535))
      (boc-error "Depth must be 0..65535, got ~A" depth))
    (%make-absent-cell hash depth 0 0 (vector hash) (vector depth))))

;; CELL-HASH, CELL-DEPTH and CELL-LEVEL are the inherited slot accessors.

;;; --- exotic cells: pruned branches and Merkle proofs/updates ---------------------

(defun cell-special-type (cell)
  "0 for an ordinary cell, else its type byte: 1 pruned branch, 2 library reference,
3 Merkle proof, 4 Merkle update."
  (%special-type (cell-exotic-p cell) (cell-bits cell) (cell-bit-length cell)))

(defun pruned-branch-p (node)
  (and (cell-p node) (= 1 (cell-special-type node))))

(defun make-pruned-branch (node &key (level 1))
  "The pruned branch standing in for NODE as seen at LEVEL (1..3, above NODE's own level): it
keeps every hash and depth NODE has, and adds LEVEL to the level mask."
  (unless (and (<= 1 level 3) (> level (node-level node)))
    (boc-error "A pruned branch at level ~D needs a node below that level (this one has level ~D)"
               level (node-level node)))
  (let* ((mask (logior (node-level-mask node) (ash 1 (1- level))))
         (b (store-uint (store-uint (begin-cell :exotic t) 1 8) mask 8)))
    (loop for h across (node-hashes node) do (setf b (store-bytes b h)))
    (loop for d across (node-depths node) do (setf b (store-uint b d 16)))
    (end-cell b)))

(defun %hash-arg (hash)
  (if (stringp hash) (hex->octets hash) (as-octets hash)))

(defun merkle-proof-root (proof)
  "The tree a Merkle proof cell attests (pruned branches included)."
  (unless (and (cell-p proof) (= 3 (cell-special-type proof)))
    (boc-error "Not a Merkle proof: ~S" proof))
  (svref (cell-refs proof) 0))

(defun verify-merkle-proof (proof expected-hash)
  "The tree PROOF attests, provided PROOF is a Merkle proof of a tree whose (level-0) hash is
EXPECTED-HASH.  Cell construction has already checked that the proof's stated hash and depth are
the tree's, pruned branches seen at level 0 as the subtrees they stand for."
  (let ((root (merkle-proof-root proof)))
    (unless (equalp (node-hash-at root 0) (%hash-arg expected-hash))
      (boc-error "Merkle proof is of ~A, expected ~A"
                 (octets->hex (node-hash-at root 0)) (octets->hex (%hash-arg expected-hash))))
    root))

(defun merkle-update-hashes (update)
  "(VALUES OLD-HASH NEW-HASH) a Merkle update cell states (checked against its subtrees at construction)."
  (unless (and (cell-p update) (= 4 (cell-special-type update)))
    (boc-error "Not a Merkle update: ~S" update))
  (values (%field-octets (cell-bits update) (cell-bit-length update) 8 32)
          (%field-octets (cell-bits update) (cell-bit-length update) 264 32)))

(defun verify-merkle-update (update expected-old-hash)
  "(VALUES NEW-HASH OLD-TREE NEW-TREE) of a Merkle update cell, provided it transforms the state
whose hash is EXPECTED-OLD-HASH."
  (unless (and (cell-p update) (= 4 (cell-special-type update)))
    (boc-error "Not a Merkle update: ~S" update))
  (let ((old (svref (cell-refs update) 0)) (new (svref (cell-refs update) 1)))
    (unless (equalp (node-hash-at old 0) (%hash-arg expected-old-hash))
      (boc-error "Merkle update starts from ~A, expected ~A"
                 (octets->hex (node-hash-at old 0)) (octets->hex (%hash-arg expected-old-hash))))
    (values (node-hash-at new 0) old new)))
(defun cell-hash-hex (cell) (node-hash-hex cell))

(defun cell-uint (cell start bit-length)
  "The unsigned integer stored in bits START .. START+BIT-LENGTH-1 of CELL."
  (unless (<= 0 start (+ start bit-length) (cell-bit-length cell))
    (boc-error "Bit range ~D..~D outside the cell's ~D bits"
               start (+ start bit-length) (cell-bit-length cell)))
  (ldb (byte bit-length (- (cell-bit-length cell) start bit-length)) (cell-bits cell)))

(defun cell-bit (cell index)
  (cell-uint cell index 1))

(defun cell-bit-vector (cell)
  (coerce (loop for i below (cell-bit-length cell) collect (cell-bit cell i)) 'bit-vector))

(defun cell-data-octets (cell)
  (data-octets (cell-bits cell) (cell-bit-length cell)))

;;; ---------------------------------------------------------------------
;;; Builder: an immutable accumulator of bits and references.
;;;
;;; Data is kept as an integer plus a bit count, so appending is a shift
;;; and an OR, and no intermediate arrays are copied.
;;; ---------------------------------------------------------------------

(defstruct (builder (:constructor %make-builder (bits bit-length refs exotic-p))
                    (:copier nil)
                    (:predicate builder-p))
  (bits 0 :type unsigned-byte :read-only t)
  (bit-length 0 :type (integer 0 1023) :read-only t)
  (refs '() :type list :read-only t)            ; most recently stored first
  (exotic-p nil :type boolean :read-only t))

(defun begin-cell (&key exotic)
  (%make-builder 0 0 '() (and exotic t)))

(defun store-bits (builder value bit-length)
  "Return BUILDER with the low BIT-LENGTH bits of the non-negative integer
VALUE appended, most significant bit first."
  (let ((new-length (+ (builder-bit-length builder) bit-length)))
    (unless (and (integerp value) (<= 0 value) (< value (ash 1 bit-length)))
      (boc-error "Value ~A does not fit in ~D unsigned bits" value bit-length))
    (when (> new-length 1023)
      (boc-error "Cell data overflow: ~D + ~D bits exceed 1023"
                 (builder-bit-length builder) bit-length))
    (%make-builder (logior (ash (builder-bits builder) bit-length) value)
                   new-length (builder-refs builder) (builder-exotic-p builder))))

(defun store-bit (builder bit)
  "BIT is 0/1 or NIL/T."
  (store-bits builder (if (member bit '(0 nil)) 0 1) 1))

(defun store-uint (builder value bit-length)
  (store-bits builder value bit-length))

(defun store-int (builder value bit-length)
  "Store VALUE as a BIT-LENGTH-bit two's complement integer."
  (unless (and (integerp value) (plusp bit-length)
               (<= (- (ash 1 (1- bit-length))) value (1- (ash 1 (1- bit-length)))))
    (boc-error "Value ~A does not fit in ~D signed bits" value bit-length))
  (store-bits builder (ldb (byte bit-length 0) value) bit-length))

(defun store-bytes (builder bytes)
  (let ((octets (as-octets bytes)))
    (store-bits builder (octets->uint octets) (* 8 (length octets)))))

(defun store-bit-vector (builder bit-vector)
  (store-bits builder
              (reduce (lambda (acc bit) (logior (ash acc 1) bit)) bit-vector :initial-value 0)
              (length bit-vector)))

(defun store-ref (builder node)
  (unless (node-p node)
    (boc-error "A reference must be a cell or an absent cell: ~S" node))
  (when (>= (length (builder-refs builder)) 4)
    (boc-error "Cell already has 4 references"))
  (%make-builder (builder-bits builder) (builder-bit-length builder)
                 (cons node (builder-refs builder)) (builder-exotic-p builder)))

(defun store-builder (builder other)
  "Append OTHER's data bits and references to BUILDER."
  (reduce #'store-ref (reverse (builder-refs other))
          :initial-value (store-bits builder (builder-bits other) (builder-bit-length other))))

(defun end-cell (builder)
  (make-cell :bits (builder-bits builder)
             :bit-length (builder-bit-length builder)
             :refs (reverse (builder-refs builder))
             :exotic (builder-exotic-p builder)))

(defmacro build-cell (&body stores)
  "Thread a fresh builder through STORES and finish it:
  (build-cell (store-uint 1 2) (store-ref leaf))
is (end-cell (store-ref (store-uint (begin-cell) 1 2) leaf))."
  `(end-cell ,(reduce (lambda (acc form) `(,(car form) ,acc ,@(cdr form)))
                      stores :initial-value '(begin-cell))))

;;; ---------------------------------------------------------------------
;;; Collecting the DAG
;;;
;;; Cells are identified by representation hash, so structurally identical
;;; subtrees built as separate objects collapse into one BOC cell.  The
;;; result is a topological order (every cell precedes its references), in
;;; the same layout @ton/core produces: reverse post-order of a DFS that
;;; visits references right to left, i.e. pre-order for plain trees.
;;; ---------------------------------------------------------------------

(defun ensure-list (x)
  (if (listp x) x (list x)))

(defun collect-nodes (roots)
  "Return the distinct nodes reachable from ROOTS (a node or a list of
nodes), deduplicated by representation hash, in topological order.  When
the same hash is reachable both as an ABSENT-CELL and as a real CELL, the
real cell wins."
  (let ((roots (ensure-list roots))
        (resolved (make-hash-table))            ; hash-key -> canonical node
        (walked (make-hash-table :test #'eq))   ; object -> T
        (seen (make-hash-table)))               ; hash-key -> T
    (labels ((resolve (node)
               ;; Walk the object graph once (by identity) and pick, for
               ;; every hash, a real CELL over an ABSENT-CELL twin.
               (unless (gethash node walked)
                 (setf (gethash node walked) t)
                 (let ((known (gethash (hash-key node) resolved)))
                   (when (or (null known) (and (absent-cell-p known) (cell-p node)))
                     (setf (gethash (hash-key node) resolved) node)))
                 (when (cell-p node)
                   (map nil #'resolve (cell-refs node)))))
             (canonical (node)
               (gethash (hash-key node) resolved))
             (visit (acc node)
               (let ((key (hash-key node)))
                 (if (gethash key seen)
                     acc
                     (progn
                       (setf (gethash key seen) t)
                       (cons node
                             (if (cell-p node)
                                 (reduce (lambda (acc ref) (visit acc (canonical ref)))
                                         (reverse (cell-refs node)) :initial-value acc)
                                 acc)))))))
      (map nil #'resolve roots)
      (reduce (lambda (acc root) (visit acc (canonical root)))
              (reverse roots) :initial-value '()))))

;;; ---------------------------------------------------------------------
;;; CRC32C (Castagnoli), appended little-endian when has_crc32c is set.
;;; ---------------------------------------------------------------------

(defparameter *crc32c-table*
  (flet ((entry (n)
           (labels ((shift (c k)
                      (if (zerop k)
                          c
                          (shift (if (logbitp 0 c)
                                     (logxor #x82F63B78 (ash c -1))
                                     (ash c -1))
                                 (1- k)))))
             (shift n 8))))
    (make-array 256 :element-type '(unsigned-byte 32)
                    :initial-contents (loop for n below 256 collect (entry n)))))

(defun crc32c (octets)
  (logxor #xFFFFFFFF
          (reduce (lambda (crc b)
                    (logxor (aref *crc32c-table* (logand #xFF (logxor crc b)))
                            (ash crc -8)))
                  octets :initial-value #xFFFFFFFF)))

(defun crc32c-octets (octets)
  (let ((crc (crc32c octets)))
    (octets (ldb (byte 8 0) crc) (ldb (byte 8 8) crc)
            (ldb (byte 8 16) crc) (ldb (byte 8 24) crc))))

;;; ---------------------------------------------------------------------
;;; Serialization
;;; ---------------------------------------------------------------------

(defconstant +boc-magic+ #xb5ee9c72)

(defun serialize-node (node index ref-bytes inline-hash-p)
  "One cell body.  INDEX maps hash keys to positions in the cell list."
  (flet ((ref-index (ref)
           (uint->octets (gethash (hash-key ref) index) ref-bytes)))
    (etypecase node
      (absent-cell
       (concat-octets (list (octets (d1-byte 7 nil (node-level-mask node) :with-hashes t) 0)
                            (node-hash node)
                            (uint->octets (node-depth node) 2))))
      (cell
       (let ((refs (cell-refs node)))
         (concat-octets
          (list* (octets (d1-byte (length refs) (cell-exotic-p node) (node-level-mask node)
                                  :with-hashes inline-hash-p)
                         (d2-byte (cell-bit-length node)))
                 ;; every significant level's hash, then every depth
                 (if inline-hash-p
                     (concat-octets (append (coerce (node-hashes node) 'list)
                                            (map 'list (lambda (d) (uint->octets d 2)) (node-depths node))))
                     (octets))
                 (cell-data-octets node)
                 (map 'list #'ref-index refs))))))))

(defun hash-inlining-predicate (with-hashes roots)
  (etypecase with-hashes
    (null (constantly nil))
    ((eql :all) (constantly t))
    ((eql :root) (lambda (node) (member node roots :test #'node-equal)))
    ((or function symbol) with-hashes)))

(defun serialize-boc (roots &key (has-idx nil) (has-crc32c t) (with-hashes nil)
                                 (threads *worker-count*))
  "Serialize the DAG reachable from ROOTS (a node or a list of nodes) into
a BOC, returned as OCTETS.

  HAS-IDX      include the per-cell offset index
  HAS-CRC32C   append a CRC32C of everything before it
  WITH-HASHES  hash inlining (h = 1 in d1): NIL, :ROOT (roots only), :ALL,
               or a predicate called with each cell.  Absent cells always
               carry their hash.
  THREADS      SB-THREAD threads for serializing cell bodies once the BOC
               has at least *PARALLEL-THRESHOLD* cells."
  (let* ((roots (ensure-list roots))
         (nodes (collect-nodes roots))
         (n (length nodes))
         (index (let ((table (make-hash-table)))
                  (loop for node in nodes for i from 0
                        do (setf (gethash (hash-key node) table) i))
                  table))
         (ref-bytes (bytes-needed n))
         (inline-hash-p (hash-inlining-predicate with-hashes roots))
         (serialize (lambda (node)
                      (serialize-node node index ref-bytes (funcall inline-hash-p node))))
         ;; INDEX is only read from here on: SBCL hash tables allow any
         ;; number of concurrent readers when nobody writes.
         (bodies (if (>= n *parallel-threshold*)
                     (pmap serialize nodes :threads threads)
                     (mapcar serialize nodes)))
         (total-size (reduce #'+ bodies :key #'length))
         (offset-bytes (bytes-needed total-size))
         (absent-count (count-if #'absent-cell-p nodes)))
    (when (or (> ref-bytes 4) (> offset-bytes 8))
      (boc-error "BOC too large: ~D cells, ~D bytes" n total-size))
    (let* ((header
             (concat-octets
              (list (uint->octets +boc-magic+ 4)
                    ;; has_idx:1 has_crc32c:1 has_cache_bits:1 flags:2 size:3
                    (octets (logior (if has-idx #x80 0) (if has-crc32c #x40 0) ref-bytes)
                            offset-bytes)
                    (uint->octets n ref-bytes)                 ; cells
                    (uint->octets (length roots) ref-bytes)    ; roots
                    (uint->octets absent-count ref-bytes)      ; absent
                    (uint->octets total-size offset-bytes)     ; tot_cells_size
                    (concat-octets                             ; root_list
                     (mapcar (lambda (root) (uint->octets (gethash (hash-key root) index) ref-bytes))
                             roots))
                    (if has-idx                                ; index
                        (concat-octets
                         (loop for body in bodies
                               for offset = (length body) then (+ offset (length body))
                               collect (uint->octets offset offset-bytes)))
                        (octets)))))
           (payload (concat-octets (cons header bodies))))
      (if has-crc32c
          (concat-octets (list payload (crc32c-octets payload)))
          payload))))

;;; ---------------------------------------------------------------------
;;; Parsing
;;; ---------------------------------------------------------------------

(defstruct (raw-cell (:copier nil))
  "One cell body as read from the wire, before references are resolved."
  (absent-p nil :read-only t)
  (exotic-p nil :read-only t)
  (level-mask 0 :read-only t)
  (hashes nil :read-only t)              ; only when h = 1: one per significant level
  (depths nil :read-only t)              ; ... likewise
  (bits 0 :read-only t)
  (bit-length 0 :read-only t)
  (ref-indices '() :read-only t))

(defun unpack-data (data padded-p)
  "Inverse of DATA-OCTETS: (values bits bit-length)."
  (let ((int (octets->uint data))
        (nbits (* 8 (length data))))
    (if (not padded-p)
        (values int nbits)
        (let ((trailing-zeros (if (zerop int) 8 (1- (integer-length (logand int (- int)))))))
          (when (>= trailing-zeros 7)
            (boc-error "Invalid completion tag in cell data ~A" (octets->hex data)))
          (values (ash int (- (1+ trailing-zeros)))
                  (- nbits 1 trailing-zeros))))))

(defun parse-raw-cell (boc pos end ref-bytes)
  "Parse the cell body starting at POS; returns (RAW-CELL . NEXT-POS)."
  (flet ((u (p n)
           (if (<= (+ p n) end)
               (octets->uint boc :start p :end (+ p n))
               (boc-error "Truncated cell at offset ~D" p)))
         (sub (p n)
           (if (<= (+ p n) end)
               (subseq boc p (+ p n))
               (boc-error "Truncated cell at offset ~D" p))))
    (let* ((d1 (u pos 1))
           (d2 (u (1+ pos) 1))
           (refs-count (logand d1 7))
           (exotic-p (logbitp 3 d1))
           (with-hashes (logbitp 4 d1))
           (level-mask (ash d1 -5))
           (absent-p (= refs-count 7)))
      (when (and (> refs-count 4) (not (and absent-p with-hashes)))
        (boc-error "Invalid descriptor byte #x~2,'0x at offset ~D" d1 pos))
      (when (and absent-p (plusp level-mask))
        (boc-error "An absent cell at offset ~D has level mask ~D" pos level-mask))
      (let* ((hash-count (1+ (logcount level-mask)))
             (hashes (and with-hashes
                          (loop for j below hash-count collect (sub (+ pos 2 (* 32 j)) 32))))
             (depths (and with-hashes
                          (loop for j below hash-count collect (u (+ pos 2 (* 32 hash-count) (* 2 j)) 2))))
             (data-pos (+ pos 2 (if with-hashes (* 34 hash-count) 0)))
             (data-length (ceiling d2 2))
             (refs-pos (+ data-pos data-length))
             (ref-indices (if absent-p
                              '()
                              (loop for j below refs-count
                                    collect (u (+ refs-pos (* j ref-bytes)) ref-bytes)))))
        (multiple-value-bind (bits bit-length) (unpack-data (sub data-pos data-length) (oddp d2))
          (cons (make-raw-cell :absent-p absent-p :exotic-p exotic-p :level-mask level-mask
                               :hashes hashes :depths depths
                               :bits bits :bit-length bit-length :ref-indices ref-indices)
                (+ refs-pos (* (length ref-indices) ref-bytes))))))))

(defun parse-raw-cells (boc start end count ref-bytes)
  "The COUNT consecutive cell bodies in BOC between START and END."
  (loop for i below count
        for (raw . next) = (parse-raw-cell boc start end ref-bytes)
          then (parse-raw-cell boc next end ref-bytes)
        collect raw into raws
        finally (progn
                  (unless (= next end)
                    (boc-error "Cell data has ~D trailing bytes" (- end next)))
                  (return raws))))

(defun link-raw-cells (raws)
  "Turn RAWS (in BOC order) into nodes.  References point forward, so
building from the last cell backwards always finds finished children."
  (let* ((raws (coerce raws 'simple-vector))
         (n (length raws))
         (nodes (make-array n)))
    (flet ((build (i raw)
             (if (raw-cell-absent-p raw)
                 (make-absent-cell (first (raw-cell-hashes raw)) :depth (first (raw-cell-depths raw)))
                 (let ((cell (make-cell
                              :bits (raw-cell-bits raw)
                              :bit-length (raw-cell-bit-length raw)
                              :exotic (raw-cell-exotic-p raw)
                              :refs (mapcar (lambda (j)
                                              (unless (< i j n)
                                                (boc-error "Cell ~D references cell ~D; references must point forward" i j))
                                              (aref nodes j))
                                            (raw-cell-ref-indices raw)))))
                   (unless (= (raw-cell-level-mask raw) (node-level-mask cell))
                     (boc-error "Cell ~D declares level mask ~D but its contents give ~D"
                                i (raw-cell-level-mask raw) (node-level-mask cell)))
                   (when (and (raw-cell-hashes raw)
                              (not (and (every #'equalp (raw-cell-hashes raw) (node-hashes cell))
                                        (every #'= (raw-cell-depths raw) (node-depths cell)))))
                     (boc-error "Inlined hashes/depths of cell ~D do not match its contents" i))
                   cell))))
      (loop for i from (1- n) downto 0
            do (setf (aref nodes i) (build i (aref raws i))))
      nodes)))

(defun parse-boc (octets &key (check-crc t))
  "Parse a serialized BOC.  Returns (values ROOTS NODES): ROOTS is the list
of root nodes and NODES the vector of all nodes in BOC order.  Inlined
hashes and depths are verified against the cell contents, and the CRC32C
is verified unless CHECK-CRC is NIL."
  (let* ((boc (as-octets octets))
         (total-length (length boc)))
    (flet ((u (pos n)
             (if (<= (+ pos n) total-length)
                 (octets->uint boc :start pos :end (+ pos n))
                 (boc-error "Truncated BOC header at offset ~D" pos))))
      (unless (= (u 0 4) +boc-magic+)
        (boc-error "Bad BOC magic #x~8,'0x" (u 0 4)))
      (let* ((flags (u 4 1))
             (has-idx (logbitp 7 flags))
             (has-crc32c (logbitp 6 flags))
             (ref-bytes (logand flags 7))
             (offset-bytes (u 5 1))
             (cell-count (u 6 ref-bytes))
             (root-count (u (+ 6 ref-bytes) ref-bytes))
             (absent-count (u (+ 6 (* 2 ref-bytes)) ref-bytes))
             (total-size (u (+ 6 (* 3 ref-bytes)) offset-bytes))
             (root-list-pos (+ 6 (* 3 ref-bytes) offset-bytes))
             (root-indices (loop for i below root-count
                                 collect (u (+ root-list-pos (* i ref-bytes)) ref-bytes)))
             (index-pos (+ root-list-pos (* root-count ref-bytes)))
             (data-pos (+ index-pos (if has-idx (* cell-count offset-bytes) 0)))
             (data-end (+ data-pos total-size))
             (expected-length (+ data-end (if has-crc32c 4 0))))
        (unless (zerop (logand flags #x18))
          (boc-error "Reserved BOC flags are set: #x~2,'0x" flags))
        (when (logbitp 5 flags)
          (boc-error "BOC has_cache_bits is not supported"))
        (unless (and (<= 1 ref-bytes 4) (<= 1 offset-bytes 8))
          (boc-error "Invalid size fields: size ~D, off_bytes ~D" ref-bytes offset-bytes))
        (unless (and (<= 1 root-count) (<= (+ root-count absent-count) cell-count))
          (boc-error "Invalid counts: ~D cells, ~D roots, ~D absent" cell-count root-count absent-count))
        (unless (every (lambda (i) (< i cell-count)) root-indices)
          (boc-error "Root index out of range: ~A" root-indices))
        (unless (= expected-length total-length)
          (boc-error "BOC length mismatch: header implies ~D bytes, got ~D" expected-length total-length))
        (when (and has-crc32c check-crc
                   (not (equalp (crc32c-octets (subseq boc 0 data-end)) (subseq boc data-end))))
          (boc-error "CRC32C mismatch"))
        (let ((nodes (link-raw-cells (parse-raw-cells boc data-pos data-end cell-count ref-bytes))))
          (unless (= absent-count (count-if #'absent-cell-p nodes))
            (boc-error "Header announces ~D absent cells, found ~D"
                       absent-count (count-if #'absent-cell-p nodes)))
          (values (mapcar (lambda (i) (aref nodes i)) root-indices)
                  nodes))))))

;;; ---------------------------------------------------------------------
;;; Demo, matching the worked example from
;;; https://docs.ton.org/foundations/serialization/boc :
;;;   a 2-bit root cell referencing a 24-bit cell and an 8-bit cell, where
;;;   the 8-bit cell itself references an identical 24-bit cell.
;;; The two 24-bit cells are deliberately built as separate objects; the
;;; BOC contains them once.
;;; ---------------------------------------------------------------------

(defun demo-root ()
  (let* ((leaf-a (build-cell (store-uint #x0aaaaa 24)))
         (leaf-b (build-cell (store-uint #x0aaaaa 24)))
         (mid (build-cell (store-uint #xfe 8) (store-ref leaf-b))))
    (build-cell (store-uint #b01 2) (store-ref leaf-a) (store-ref mid))))

;;; ---------------------------------------------------------------------
;;; Self-test.  Reference values were produced with @ton/core.
;;; ---------------------------------------------------------------------

(defun boc-roundtrip (roots &rest options)
  "Serialize then parse; returns the parsed roots."
  (values (parse-boc (apply #'serialize-boc roots options))))

(defun run-boc-tests ()
  "Run the self-test; returns T on success, otherwise a list of failures."
  (let ((failures '()))
    (macrolet ((check (name form)
                 `(handler-case
                      (unless ,form (push (list ,name ',form) failures))
                    (error (e) (push (list ,name (princ-to-string e)) failures))))
               (check-signals (name form)
                 `(check ,name (handler-case (progn ,form nil) (boc-error () t)))))
      (let* ((root (demo-root))
             (empty (build-cell))
             (inner (build-cell (store-uint 456 16)))
             (r2 (build-cell (store-uint 0 64) (store-ref inner)))
             (chain (reduce (lambda (child i) (build-cell (store-uint i 32) (store-ref child)))
                            (loop for i below 300 collect i)
                            :initial-value (build-cell (store-uint 7 3))))
             (wide (labels ((wide (d tag)
                              (end-cell
                               (reduce #'store-ref
                                       (if (plusp d)
                                           (loop for i below 4 collect (wide (1- d) (+ (* 4 tag) i)))
                                           '())
                                       :initial-value (store-uint (begin-cell) tag 16)))))
                     (wide 3 1))))
        ;; hashes and layout vs @ton/core
        (check "empty cell hash"
               (string= (cell-hash-hex empty)
                        "96a296d224f285c67bee93c30f8a309157f0daa35dc5b87e410b78630a09cfc7"))
        (check "empty cell boc"
               (string= (octets->hex (serialize-boc empty :has-crc32c nil)) "b5ee9c72010101010002000000"))
        (check "docs example hash"
               (string= (cell-hash-hex root)
                        "b6249823033847bb521169047f04e0fb14f2be6f74b5add53a5a264cdd23e8fe"))
        (check "docs example dedups 4 cells into 3" (= 3 (length (collect-nodes root))))
        (check "docs example boc with index"
               (string= (octets->hex (serialize-boc root :has-idx t :has-crc32c nil))
                        "b5ee9c7281010301000e0005090e02016002010102fe0200060aaaaa"))
        (check "docs example boc with crc32c"
               (string= (octets->hex (serialize-boc root))
                        "b5ee9c7241010301000e0002016002010102fe0200060aaaaa4f0cafd9"))
        (check "64 zero bits + ref"
               (and (string= (cell-hash-hex r2)
                             "3fff0abddb5c8536d4015a08d22a7e16e73dac5d04d12ada73274900ea65ba93")
                    (string= (octets->hex (serialize-boc r2 :has-crc32c nil))
                             "b5ee9c7201010201000f000110000000000000000001000401c8")))
        (check "chain of 301 cells"
               (and (= (cell-depth chain) 300)
                    (string= (cell-hash-hex chain)
                             "68a4b3352d834f70da822145ef4c0b99de2cf31ba7e37a09d4e0b3a8ca961803")
                    (string= (octets->hex (sha256 (serialize-boc chain)))
                             "93a34bc0e11a8786b476071f51410bb79225839927ce11b863ce8c25b23955ef")
                    (string= (octets->hex (sha256 (serialize-boc chain :has-idx t)))
                             "3317328578263a3f04f9d8aec0bb54ef7a90879cec770d5be27fbf96e9512839")))
        (check "wide tree of 85 cells"
               (and (string= (cell-hash-hex wide)
                             "3ffa8ac49043351e3553ba11dde79498c27ebf7335ec3f495761a87e91157e43")
                    (string= (octets->hex (sha256 (serialize-boc wide :has-crc32c nil)))
                             "51b299285aea7003bc38b4b82d674d9001b16e1670bb467794ddfbcc0f806ee4")))
        (check "crc32c test vector"
               (= (crc32c (map 'octets #'char-code "123456789")) #xE3069283))
        ;; threads: same bytes regardless of thread count
        (check "parallel serialization is deterministic"
               (let ((one (serialize-boc chain :threads 1))
                     (many (serialize-boc chain :threads 7))
                     (max (serialize-boc chain :threads 1000)))
                 (and (equalp one many) (equalp one max))))
        (check "pmap preserves order and builds cells"
               (let ((items (loop for i below 1000 collect i)))
                 (equal (mapcar #'cell-hash-hex (pmap (lambda (i) (build-cell (store-uint i 32))) items))
                        (mapcar (lambda (i) (cell-hash-hex (build-cell (store-uint i 32)))) items))))
        (check-signals "pmap re-signals worker errors"
                       (pmap (lambda (i) (build-cell (store-uint i 2))) (loop for i below 100 collect i)))
        ;; round trips
        (check "round trip plain"
               (node-equal chain (first (boc-roundtrip chain))))
        (check "round trip with index and crc"
               (node-equal wide (first (boc-roundtrip wide :has-idx t :has-crc32c t))))
        (check "round trip with root hash inlined"
               (let ((boc (serialize-boc root :with-hashes :root :has-crc32c nil)))
                 (and (= (aref boc (+ 4 1 1 1 1 1 1 1)) (+ 2 16))        ; d1 of the root has h = 1
                      (node-equal root (first (parse-boc boc))))))
        (check "round trip with all hashes inlined"
               (and (node-equal wide (first (boc-roundtrip wide :with-hashes :all)))
                    (= (length (serialize-boc wide :with-hashes :all :has-crc32c nil))
                       (+ (length (serialize-boc wide :has-crc32c nil)) (* 85 34)))))
        (check "round trip with predicate hash inlining"
               (node-equal wide (first (boc-roundtrip wide :with-hashes (lambda (c) (> (cell-depth c) 1))))))
        (check "round trip multiple roots"
               (let ((roots (boc-roundtrip (list root r2 empty) :has-idx t)))
                 (and (= 3 (length roots))
                      (every #'node-equal roots (list root r2 empty)))))
        (check "parse rejects corrupted crc"
               (let ((boc (copy-seq (serialize-boc root))))
                 (setf (aref boc (1- (length boc))) (logxor 1 (aref boc (1- (length boc)))))
                 (handler-case (progn (parse-boc boc) nil) (boc-error () t))))
        (check "parse rejects corrupted inlined hash"
               (let ((boc (copy-seq (serialize-boc root :with-hashes :root :has-crc32c nil))))
                 (setf (aref boc 15) (logxor 1 (aref boc 15)))
                 (handler-case (progn (parse-boc boc) nil) (boc-error () t))))
        ;; absent cells
        (let* ((leaf (build-cell (store-uint #x0aaaaa 24)))
               (ghost (make-absent-cell (cell-hash leaf) :depth (cell-depth leaf)))
               (with-ghost (build-cell (store-uint #xfe 8) (store-ref ghost)))
               (with-leaf (build-cell (store-uint #xfe 8) (store-ref leaf))))
          (check "absent ref hashes like the real cell"
                 (node-equal with-ghost with-leaf))
          (check "absent cell serialized and counted"
                 (let ((boc (serialize-boc with-ghost :has-crc32c nil)))
                   (and (= (aref boc 8) 1)                       ; absent count
                        (= (length boc) (+ 4 1 1 1 1 1 1 1 4 (+ 2 32 2)))
                        (multiple-value-bind (roots nodes) (parse-boc boc)
                          (and (node-equal (first roots) with-ghost)
                               (absent-cell-p (aref nodes 1))
                               (= 0 (node-depth (aref nodes 1)))
                               (equalp (node-hash (aref nodes 1)) (cell-hash leaf)))))))
          (check "real cell wins over absent twin"
                 (let ((nodes (collect-nodes (build-cell (store-ref ghost) (store-ref with-leaf)))))
                   (and (= 3 (length nodes)) (notany #'absent-cell-p nodes))))
          (check "real cell wins when first seen absent"
                 (let ((nodes (collect-nodes (list with-ghost with-leaf))))
                   (and (= 2 (length nodes)) (notany #'absent-cell-p nodes)))))
        ;; builder semantics
        (check "builder is persistent"
               (let* ((b (store-uint (begin-cell) 5 3))
                      (b1 (store-uint b 1 1))
                      (b2 (store-uint b 0 1)))
                 (and (= 3 (builder-bit-length b))
                      (= #b1011 (builder-bits b1))
                      (= #b1010 (builder-bits b2)))))
        (check "store-int two's complement"
               (= (cell-uint (build-cell (store-int -1 8) (store-int -128 8) (store-int 127 8)) 0 24)
                  #xff807f))
        (check "store-bytes / store-bit-vector / store-builder"
               (let ((c (build-cell (store-builder (store-bytes (begin-cell) (octets 1 2)))
                                    (store-bit-vector #*101)
                                    (store-ref inner))))
                 (and (= 19 (cell-bit-length c))
                      (equalp (cell-bit-vector c) #*0000000100000010101)
                      (equalp (cell-data-octets c) (octets 1 2 #b10110000))
                      (= 1 (length (cell-refs c))))))
        (check-signals "1024 bits overflow" (store-uint (store-uint (begin-cell) 0 1023) 0 1))
        (check-signals "5 refs overflow"
                       (reduce #'store-ref (make-list 5 :initial-element empty) :initial-value (begin-cell)))
        (check-signals "value too large" (store-uint (begin-cell) 4 2))
        (check-signals "bad magic" (parse-boc (octets 1 2 3 4 5 6 7 8 9 10)))))
    (if failures
        (progn
          (format t "~D test~:P FAILED:~%~{  ~A~%~}" (length failures) (mapcar #'first failures))
          (reverse failures))
        (progn
          (format t "all tests passed~%")
          t))))
