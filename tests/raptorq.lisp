;;;; tests/raptorq.lisp -- RaptorQ (src/raptorq.lisp) against the node's own encoder and against itself.
;;;;
;;;; fixtures/raptorq/oracle.txt holds encoding symbols produced by the node's compiled tdfec encoder (ton-2026.10), for data
;;;; that is reproducible here (see %RQ-T-DATA); the encoder must reproduce every one of them octet for octet, which pins the
;;;; tables, the tuple generator, the LDPC/HDPC rows and the solver.  The decoder is then checked on loss patterns up to "every
;;;; source symbol lost", and the small algebra (GF(256), XOR) against naive versions.

(in-package :cl-ton/test)

(defun %rq-t-data (size seed)
  "The data the oracle fixture was made from: octet i = ((i*131 + seed*17) xor (i>>7) xor ((i*i)>>5)) and 255."
  (let ((v (make-array size :element-type '(unsigned-byte 8))))
    (dotimes (i size v)
      (setf (aref v i) (ldb (byte 8 0) (logxor (+ (* i 131) (* seed 17)) (ash i -7) (ash (* i i) -5)))))))

(defun %rq-t-hex (string)
  (let ((v (make-array (/ (length string) 2) :element-type '(unsigned-byte 8))))
    (dotimes (i (length v) v)
      (setf (aref v i) (parse-integer string :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))))

(defun %rq-t-split (line)
  (let ((out '()) (start 0))
    (loop for i from 0 to (length line)
          do (when (or (= i (length line)) (char= (char line i) #\Space))
               (push (subseq line start i) out)
               (setf start (1+ i))))
    (nreverse out)))

(defun %rq-t-oracle-cases ()
  "A list of (data-size symbol-size seed ((id . symbol) ...)) read from the fixture file."
  (let ((path (merge-pathnames "fixtures/raptorq/oracle.txt"
                               (make-pathname :name nil :type nil :version nil
                                              :defaults #.(or *compile-file-truename* *load-truename*))))
        (cases '()))
    (with-open-file (in path)
      (loop for line = (read-line in nil) while line
            do (let ((parts (%rq-t-split line)))
                 (cond ((string= (first parts) "CASE")
                        (push (list (parse-integer (second parts)) (parse-integer (third parts))
                                    (parse-integer (fourth parts)) '())
                              cases))
                       ((string= (first parts) "SYM")
                        (push (cons (parse-integer (second parts)) (%rq-t-hex (third parts))) (fourth (first cases))))))))
    (nreverse cases)))

(defun %rq-t-shuffle (list state)
  (let ((v (coerce list 'vector)))
    (loop for i from (1- (length v)) downto 1 do (rotatef (aref v i) (aref v (random (1+ i) state))))
    (coerce v 'list)))

(defun %rq-t-decode (data symbol-size ids encoder)
  "Feed the symbols IDS (in the given order) of ENCODER to a decoder of DATA and return its result."
  (let ((dec (cl-ton::make-rq-decoder (length data) symbol-size)))
    (dolist (id ids) (cl-ton::rq-decoder-add dec id (cl-ton::rq-encoder-symbol encoder id)))
    (cl-ton::rq-decoder-decode dec)))

(defun test-raptorq ()
  ;; --- the algebra
  (check "GF(256): alpha^8 = 0x1D and the field polynomial reduces" (and (= (cl-ton::%rq-alpha-power 8) #x1D)
                                                                          (= (cl-ton::%rq-gf* 2 128) #x1D)))
  (check "GF(256): every nonzero element times its inverse is 1, multiplication commutes"
         (loop for a from 1 below 256
               always (and (= 1 (cl-ton::%rq-gf* a (aref cl-ton::+rq-inv+ a)))
                           (loop for b from 0 below 256 always (= (cl-ton::%rq-gf* a b) (cl-ton::%rq-gf* b a))))))
  (check "XOR and multiply-add over octet vectors equal the naive versions (sizes 0..19)"
         (let ((state (sb-ext:seed-random-state 5)))
           (loop for n from 0 below 20
                 always (let* ((a (make-array n :element-type '(unsigned-byte 8)))
                               (b (make-array n :element-type '(unsigned-byte 8)))
                               (c (random 256 state)))
                          (dotimes (i n) (setf (aref a i) (random 256 state) (aref b i) (random 256 state)))
                          (and (equalp (cl-ton::%rq-xor-into (copy-seq a) b) (map 'vector #'logxor a b))
                               (equalp (cl-ton::%rq-addmul-into (copy-seq a) b c)
                                       (map 'vector (lambda (x y) (logxor x (cl-ton::%rq-gf* c y))) a b)))))))
  ;; --- the parameters
  (check "parameters: K=1 gives K'=10, J=254, S=7, H=10, W=17; K=56403 is the last; 56404 and 0 are refused"
         (let ((p (cl-ton::rq-parameters 1)))
           (and (= (cl-ton::rqp-kp p) 10) (= (cl-ton::rqp-j p) 254) (= (cl-ton::rqp-s p) 7) (= (cl-ton::rqp-h p) 10)
                (= (cl-ton::rqp-w p) 17) (= (cl-ton::rqp-l p) 27)
                (= (cl-ton::rqp-kp (cl-ton::rq-parameters 56403)) 56403)
                (null (cl-ton::rq-parameters 56404)) (null (cl-ton::rq-parameters 0)))))
  (check "parameters: K=11 is padded to K'=12, K=300 to K'=301"
         (and (= 12 (cl-ton::rqp-kp (cl-ton::rq-parameters 11))) (= 301 (cl-ton::rqp-kp (cl-ton::rq-parameters 300)))))
  (check "parameters: P1 is the smallest prime STRICTLY above P, as the node has it (K'=49: P=11 -> 13; K'=385: P=31 -> 37; K'=300: P=27 -> 29)"
         (flet ((pp (k) (let ((p (cl-ton::rq-parameters k))) (list (cl-ton::rqp-p p) (cl-ton::rqp-p1 p)))))
           (and (equal (pp 49) '(11 13)) (equal (pp 385) '(31 37)) (equal (pp 300) '(27 29)))))
  ;; --- the node's own encoder is the oracle
  (let ((cases (%rq-t-oracle-cases)) (total 0))
    (dolist (case cases)
      (destructuring-bind (size symbol-size seed symbols) case
        (let* ((data (%rq-t-data size seed))
               (enc (cl-ton::make-rq-encoder data symbol-size))
               (bad (loop for (id . symbol) in symbols
                          unless (equalp (cl-ton::rq-encoder-symbol enc id) symbol) collect id)))
          (incf total (length symbols))
          (check (format nil "oracle: ~D octets in ~D-octet symbols (K=~D): ~D symbols equal the node's"
                         size symbol-size (cl-ton::rq-encoder-symbols-count enc) (length symbols))
                 (null bad)))))
    (check "oracle: the fixture is not empty" (and (>= (length cases) 20) (> total 100))))
  ;; --- the decoder
  (let ((state (sb-ext:seed-random-state 99)))
    (loop for (size symbol-size) in '((1 16) (100 16) (161 16) (5000 768) (20000 768) (100000 768) (300 1))
          do (let* ((data (%rq-t-data size 21))
                    (enc (cl-ton::make-rq-encoder data symbol-size))
                    (k (cl-ton::rq-encoder-symbols-count enc))
                    (sources (loop for i below k collect i))
                    (repairs (loop for i from k below (+ k k 30) collect i)))
               (check (format nil "decode ~D octets / ~D (K=~D): all source symbols, in a shuffled order" size symbol-size k)
                      (equalp data (%rq-t-decode data symbol-size (%rq-t-shuffle sources state) enc)))
               (check (format nil "decode ~D octets / ~D (K=~D): every source symbol lost, K repair symbols" size symbol-size k)
                      (equalp data (%rq-t-decode data symbol-size (%rq-t-shuffle (subseq repairs 0 k) state) enc)))
               (check (format nil "decode ~D octets / ~D (K=~D): 25% of the source symbols lost, as many repair symbols +2" size symbol-size k)
                      (let* ((kept (remove-if (lambda (i) (declare (ignore i)) (< (random 4 state) 1)) sources))
                             (need (+ 2 (- k (length kept)))))
                        (equalp data (%rq-t-decode data symbol-size
                                                   (%rq-t-shuffle (append kept (subseq repairs 0 need)) state) enc))))
               (check (format nil "decode ~D octets / ~D (K=~D): a random K+3 of all symbols (repair ids far away)" size symbol-size k)
                      (equalp data (%rq-t-decode data symbol-size
                                                 (subseq (%rq-t-shuffle (append sources repairs (list 70000 70001 1000000)) state)
                                                         0 (+ k 3))
                                                 enc))))))
  (let* ((data (%rq-t-data 5000 4)) (enc (cl-ton::make-rq-encoder data 768))
         (k (cl-ton::rq-encoder-symbols-count enc)))
    (check "decode: fewer than K symbols says :NEED-MORE, and decoding works once the rest arrives"
           (let ((dec (cl-ton::make-rq-decoder 5000 768)))
             (loop for id from 20 below (+ 20 (1- k)) do (cl-ton::rq-decoder-add dec id (cl-ton::rq-encoder-symbol enc id)))
             (and (eq :need-more (nth-value 1 (cl-ton::rq-decoder-decode dec)))
                  (cl-ton::rq-decoder-add dec 99 (cl-ton::rq-encoder-symbol enc 99))
                  (equalp data (cl-ton::rq-decoder-decode dec)))))
    (check "decode: duplicates, symbols of a wrong size and impossible ids are ignored"
           (let ((dec (cl-ton::make-rq-decoder 5000 768)))
             (loop repeat 5 do (cl-ton::rq-decoder-add dec 3 (cl-ton::rq-encoder-symbol enc 3)))
             (cl-ton::rq-decoder-add dec 4 (subseq (cl-ton::rq-encoder-symbol enc 4) 0 700))
             (cl-ton::rq-decoder-add dec (ash 1 24) (cl-ton::rq-encoder-symbol enc 5))
             (cl-ton::rq-decoder-add dec -1 (cl-ton::rq-encoder-symbol enc 5))
             (and (= 1 (hash-table-count (cl-ton::rq-decoder-symbols dec)))
                  (eq :need-more (nth-value 1 (cl-ton::rq-decoder-decode dec))))))
    (check "decode: a second call returns the same data; the last symbol is trimmed to the data size"
           (let ((dec (cl-ton::make-rq-decoder 5000 768)))
             (dolist (id (loop for i from k below (+ k k) collect i))
               (cl-ton::rq-decoder-add dec id (cl-ton::rq-encoder-symbol enc id)))
             (let ((first (cl-ton::rq-decoder-decode dec)))
               (and (= 5000 (length first)) (equalp first data) (eq first (cl-ton::rq-decoder-decode dec))))))
    (check "decoder and encoder refuse impossible sizes (no data, more than 56403 symbols)"
           (and (null (cl-ton::make-rq-decoder 0 768)) (null (cl-ton::make-rq-decoder 10 0))
                (null (cl-ton::make-rq-decoder (* 56404 16) 16))
                (null (cl-ton::make-rq-encoder (make-array (* 56404 16) :element-type '(unsigned-byte 8)) 16)))))
  ;; --- the largest transfer RLDP2 makes: a 2,000,000-octet part (K=2605), every source symbol lost
  (let* ((data (%rq-t-data 2000000 5)) (enc (cl-ton::make-rq-encoder data 768)) (k (cl-ton::rq-encoder-symbols-count enc)))
    (check "decode: a full 2,000,000-octet part (K=2605) from repair symbols only"
           (equalp data (%rq-t-decode data 768 (%rq-t-shuffle (loop for i from k below (+ k k) collect i)
                                                                (sb-ext:seed-random-state 1))
                                      enc)))))
