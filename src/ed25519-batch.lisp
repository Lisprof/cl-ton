;;;; ed25519-batch.lisp -- many Ed25519 signatures checked at once, from ironclad's own curve operations.
;;;;
;;;; Checking a chain of key-block links means checking tens of thousands of validator signatures, and
;;;; IRONCLAD:VERIFY-SIGNATURE does each one alone: two Montgomery ladders (about 1000 point operations)
;;;; and two point decompressions, ~3.8 ms.  Nothing here replaces ironclad: the point arithmetic, the
;;;; decoding, the hash and the group constants are all ironclad's (EC-ADD, EC-DOUBLE, EC-DECODE-POINT,
;;;; ED25519-HASH, +ED25519-L+ ...).  What is new is only how the work is arranged, as plain functions of
;;;; their arguments -- no I/O, no shared state beyond a memo of decoded public keys -- so it can be shared,
;;;; batched and spread over threads:
;;;;
;;;;   * a signature (R, s) by key A over message M is valid when  s*B = R + h*A,  h = H(R || A || M) mod L;
;;;;   * for N signatures and random 128-bit weights z_i the single equation
;;;;         (sum z_i s_i) * B  =  sum z_i R_i  +  sum (sum_i z_i h_i) A      (one term per distinct key A)
;;;;     holds when all are valid, and fails except with probability 2^-128 when any is not (the weights
;;;;     are derived from a hash of the whole batch, so the function stays deterministic);
;;;;   * its right side is one multi-scalar multiplication, done with the bucket method (Pippenger): the
;;;;     cost per signature falls from ~1000 point operations to a few tens, and validators that sign many
;;;;     links share one term;
;;;;   * the equation is checked multiplied by the cofactor 8 (as the batch verification of the Ed25519
;;;;     paper does), which every valid signature satisfies too.
;;;;
;;;; A batch that fails says nothing about WHICH signature is bad: ED25519-FIRST-INVALID then falls back to
;;;; ironclad's one-at-a-time verification, so refusals keep naming the culprit.

(in-package :cl-ton)

;;; --- ironclad's SBCL assembly optimizer -----------------------------------------------------------
;;;
;;; Everything cl-ton takes from ironclad (SHA-256/512, HMAC, PBKDF2, the Ed25519 curve operations, and the
;;; AES-256-CTR of every ADNL-ext connection) runs the faster code only when ironclad was built with its
;;; dedicated assembly optimizer for SBCL: the feature :IRONCLAD-ASSEMBLY (pushed by ironclad's own
;;; src/package.lisp, src/opt/sbcl/*.lisp) defines the VOPs of package IRONCLAD-VM -- AES-NI rounds and key
;;; schedule, PCLMULQDQ for GHASH, the 32/64-bit rotates and byte swaps of the hashes and stream ciphers --
;;; and picks AES-NI at run time when the CPU has it.  It is on by default; this makes losing it loud.

(defun ironclad-assembly-status ()
  "(:ASSEMBLY bool :VM-PACKAGE bool :AES-NI bool :PCLMULQDQ bool): whether ironclad was built with its SBCL
assembly optimizer, whether its VOP package is loaded, and whether the CPU lets it use AES-NI and PCLMULQDQ."
  (flet ((cpu (name)
           (let ((f (and (find-package :crypto) (find-symbol name :crypto))))
             (and f (fboundp f) (ignore-errors (and (funcall f) t))))))
    (list :assembly (and (member :ironclad-assembly *features*) t)
          :vm-package (and (find-package :ironclad-vm) t)
          :aes-ni (cpu "AES-NI-SUPPORTED-P")
          :pclmulqdq (cpu "PCLMULQDQ-SUPPORTED-P"))))

(defun ironclad-assembly-line ()
  "One line for the diagnostics: the state of ironclad's assembly optimizer."
  (destructuring-bind (&key assembly vm-package aes-ni pclmulqdq) (ironclad-assembly-status)
    (format nil "ironclad SBCL assembly optimizer: ~:[OFF (generic Lisp code; rebuild ironclad with :ironclad-assembly)~;on~]~@[ (VOPs ~:*~:[missing~;loaded~])~], AES-NI ~:[no~;yes~], PCLMULQDQ ~:[no~;yes~]"
            assembly (and assembly vm-package) aes-ni pclmulqdq)))

(eval-when (:load-toplevel :execute)
  (unless (getf (ironclad-assembly-status) :assembly)
    (warn "ironclad was built WITHOUT its SBCL assembly optimizer (feature :IRONCLAD-ASSEMBLY): the ADNL AES-CTR ~
and the hashes run the slower generic code.  Do not comment out (pushnew :ironclad-assembly *features*) in ironclad's src/package.lisp.")))

(defvar *ed25519-key-points* (make-hash-table :test #'equalp :synchronized t)
  "Memo: public key octets -> decoded ironclad point.  Decoding costs a modular square root (~0.16 ms) and
the same ~100 validators sign link after link.")

(defun ed25519-key-point (public)
  "PUBLIC (32 octets) decoded to an ironclad point; NIL when it is not a point.  Memoized."
  (let ((key (coerce public '(simple-array (unsigned-byte 8) (*)))))
    (multiple-value-bind (point found) (gethash key *ed25519-key-points*)
      (if found
          point
          (let ((point (handler-case (ironclad:ec-decode-point :ed25519 key) (error () nil))))
            (when (> (hash-table-count *ed25519-key-points*) 20000)
              (clrhash *ed25519-key-points*))
            (setf (gethash (copy-seq key) *ed25519-key-points*) point))))))

(defstruct (ed25519-item (:constructor %make-ed25519-item (public r-bytes r-point s h)))
  "A signature unpacked for batching: the key octets, R's octets and point, s and h as integers."
  public r-bytes r-point s h)

(defun ed25519-prepare (public message signature)
  "The ED25519-ITEM for SIGNATURE (64 octets) by the key PUBLIC over MESSAGE, or NIL when the signature
cannot be valid (wrong length, s not below the group order, R or the key not a curve point)."
  (let ((public (coerce public '(simple-array (unsigned-byte 8) (*))))
        (message (coerce message '(simple-array (unsigned-byte 8) (*))))
        (signature (coerce signature '(simple-array (unsigned-byte 8) (*)))))
    (when (and (= 32 (length public)) (= 64 (length signature)))
      (let* ((r-bytes (subseq signature 0 32))
             (s (ironclad:octets-to-integer signature :start 32 :end 64 :big-endian nil))
             (a (ed25519-key-point public))
             (r (handler-case (ironclad:ec-decode-point :ed25519 r-bytes) (error () nil))))
        (when (and a r (< s crypto::+ed25519-l+))
          (%make-ed25519-item
           public r-bytes r s
           (mod (ironclad:octets-to-integer (crypto::ed25519-hash r-bytes public message) :big-endian nil)
                crypto::+ed25519-l+)))))))

;;; --- multi-scalar multiplication (bucket method) -----------------------------------------------

(defun %identity-point () (ironclad:ec-make-point :ed25519 :x 0 :y 1))

(defun %msm-window (n)
  "A window width in bits for N terms: about log2 N - 2, the usual optimum of the bucket method."
  (max 2 (min 12 (- (integer-length n) 2))))

(defun %multi-scalar-mult (points scalars)
  "The sum of SCALARS[i] * POINTS[i] (non-negative integers, any size) by the bucket method: per window of
C bits, each point goes into the bucket of its digit, and the buckets are summed with a running sum."
  (let* ((n (length points))
         (c (%msm-window n))
         (bits (reduce #'max scalars :key #'integer-length :initial-value 1))
         (windows (ceiling bits c))
         (size (1- (ash 1 c)))
         (result nil))
    (loop for w from (1- windows) downto 0
          do (when result (dotimes (k c) (setf result (ironclad:ec-double result))))
             (let ((buckets (make-array size :initial-element nil)))
               (loop for p across points
                     for s across scalars
                     do (let ((d (ldb (byte c (* w c)) s)))
                          (when (plusp d)
                            (let ((b (svref buckets (1- d))))
                              (setf (svref buckets (1- d)) (if b (ironclad:ec-add b p) p))))))
               (let ((running nil) (sum nil))
                 (loop for j from (1- size) downto 0
                       do (let ((b (svref buckets j)))
                            (when b (setf running (if running (ironclad:ec-add running b) b))))
                          (when running (setf sum (if sum (ironclad:ec-add sum running) running))))
                 (when sum (setf result (if result (ironclad:ec-add result sum) sum))))))
    (or result (%identity-point))))

;;; --- batch verification --------------------------------------------------------------------------

(defun %batch-weights (items)
  "A 128-bit weight for each of ITEMS, from a hash of every signature in the batch."
  (let ((seed (ironclad:make-digest :sha512)))
    (dolist (item items)
      (ironclad:update-digest seed (ed25519-item-public item))
      (ironclad:update-digest seed (ed25519-item-r-bytes item))
      (ironclad:update-digest seed (ironclad:integer-to-octets (ed25519-item-s item) :n-bits 256 :big-endian nil))
      (ironclad:update-digest seed (ironclad:integer-to-octets (ed25519-item-h item) :n-bits 256 :big-endian nil)))
    (let ((seed (ironclad:produce-digest seed)))
      (loop for i from 0 below (length items)
            collect (max 1 (ironclad:octets-to-integer
                            (let ((d (ironclad:make-digest :sha512)))
                              (ironclad:update-digest d seed)
                              (ironclad:update-digest d (ironclad:integer-to-octets i :n-bits 32))
                              (ironclad:produce-digest d))
                            :end 16 :big-endian nil))))))

(defun ed25519-batch-verify (items)
  "True when every one of ITEMS (ED25519-ITEMs) is a valid signature -- up to a failure probability of
2^-128 the other way.  Pure: the same ITEMS always give the same answer."
  (or (null items)
      (let* ((zs (%batch-weights items))
             (order crypto::+ed25519-l+)
             (s-total (mod (loop for item in items for z in zs sum (* z (ed25519-item-s item))) order))
             (by-key (make-hash-table :test #'equalp))
             (points '()) (scalars '()))
        (loop for item in items
              for z in zs
              do (push (ed25519-item-r-point item) points)
                 (push z scalars)
                 (let ((entry (or (gethash (ed25519-item-public item) by-key)
                                  (setf (gethash (ed25519-item-public item) by-key) (cons 0 nil)))))
                   (incf (car entry) (* z (ed25519-item-h item)))))
        (maphash (lambda (public entry)
                   (push (ed25519-key-point public) points)
                   (push (mod (car entry) order) scalars))
                 by-key)
        (let ((left (%multi-scalar-mult (coerce points 'vector) (coerce scalars 'vector)))
              (right (ironclad:ec-scalar-mult crypto::+ed25519-b+ s-total)))
          (flet ((times-8 (p) (dotimes (k 3 p) (setf p (ironclad:ec-double p)))))
            (ironclad:ec-point-equal (times-8 left) (times-8 right)))))))

(defun ed25519-first-invalid (entries)
  "ENTRIES is a list of (PUBLIC MESSAGE SIGNATURE ...) -- anything after the third element is ignored.  NIL
when all are valid, else the index of the first that is not.  A batch check settles the common case at
once; only a failing batch is searched, one signature at a time with ironclad's own verification."
  (flet ((octets (x) (coerce x '(simple-array (unsigned-byte 8) (*)))))
    (let* ((items (loop for e in entries collect (ed25519-prepare (first e) (second e) (third e))))
           (bad (position nil items)))
      (cond (bad                        ; not even a well-formed signature -- but an earlier one may fail the equation
             (or (and (plusp bad) (ed25519-first-invalid (subseq entries 0 bad))) bad))
            ((ed25519-batch-verify items) nil)
            (t (or (loop for e in entries
                         for i from 0
                         unless (handler-case
                                    (ironclad:verify-signature (ironclad:make-public-key :ed25519 :y (octets (first e)))
                                                               (octets (second e)) (octets (third e)))
                                  (error () nil))
                           return i)
                   0))))))

;;; --- spreading pure jobs over the processors -------------------------------------------------------

(defvar *worker-count* nil "How many threads pure jobs may use; NIL means one per processor, at most 8.")

(defun processor-count ()
  (or (ignore-errors
       (let ((n (sb-alien:alien-funcall
                 (sb-alien:extern-alien "sysconf" (function sb-alien:long sb-alien:int)) 84))) ; _SC_NPROCESSORS_ONLN
         (and (plusp n) n)))
      1))

(defun worker-count () (or *worker-count* (min 8 (processor-count))))

(defun parallel-map (function items &key (workers (worker-count)))
  "(MAPCAR FUNCTION ITEMS) with the items dealt out to up to WORKERS threads.  FUNCTION must be pure (it
runs in a thread without the caller's dynamic bindings); an error in any call is raised here, for the
first failing item in order."
  (let ((n (length items)))
    (if (or (<= workers 1) (<= n 1))
        (mapcar function items)
        (let* ((items (coerce items 'vector))
               (results (make-array n :initial-element nil))
               (next 0)
               (lock (sb-thread:make-mutex :name "parallel-map"))
               (threads
                 (loop repeat (min workers n)
                       collect (sb-thread:make-thread
                                (lambda ()
                                  (loop
                                    (let ((i (sb-thread:with-mutex (lock) (prog1 next (incf next)))))
                                      (when (>= i n) (return))
                                      (setf (svref results i)
                                            (handler-case (list :ok (funcall function (svref items i)))
                                              (error (e) (list :error e)))))))
                                :name "pure job"))))
          (mapc #'sb-thread:join-thread threads)
          (loop for r across results
                do (when (eq (first r) :error) (error (second r))))
          (map 'list #'second results)))))
