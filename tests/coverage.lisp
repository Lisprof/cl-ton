;;;; tests/coverage.lisp -- tests for code the other suites never ran (Stage 3).
;;;;
;;;; The proxy's shard routing (%SHARD-CONTAINS-P, %SLICE-COVERS-P), the TVM tuple parser (PARSE-VM-TUPLE), the head poller's
;;;; wait (WAIT-FOR-PUBLISHED-HEAD) and the confirmed-flow scan (SCAN-CONFIRMED-FLOW-ONCE).

(in-package :cl-ton/test)

(defun %hash-starting (byte)
  (let ((h (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
    (setf (aref h 0) byte)
    h))

(defun test-proxy-shard-routing ()
  (format t "proxy shard routing: which shard holds an account, which slice serves a query~%")
  (let ((whole (- (expt 2 63)))          ; 0x8000...: the whole workchain
        (left #x4000000000000000)        ; prefix 0
        (right (- #x4000000000000000))   ; 0xC000...: prefix 1
        (left-right #x6000000000000000)) ; prefix 01
    (check "the whole-workchain shard holds every account"
           (and (cl-ton::%shard-contains-p whole (%hash-starting #x00))
                (cl-ton::%shard-contains-p whole (%hash-starting #xFF))))
    (check "the two halves split by the first bit of the account"
           (and (cl-ton::%shard-contains-p left (%hash-starting #x7F))
                (not (cl-ton::%shard-contains-p left (%hash-starting #x80)))
                (cl-ton::%shard-contains-p right (%hash-starting #x80))
                (not (cl-ton::%shard-contains-p right (%hash-starting #x7F)))))
    (check "a deeper shard looks at two bits"
           (and (cl-ton::%shard-contains-p left-right (%hash-starting #x40))
                (cl-ton::%shard-contains-p left-right (%hash-starting #x7F))
                (not (cl-ton::%shard-contains-p left-right (%hash-starting #x3F)))
                (not (cl-ton::%shard-contains-p left-right (%hash-starting #x80)))))
    (flet ((q (&rest args) (apply #'cl-ton::make-qinfo args)))
      (let ((slice (list :shards (list (cons 0 left)) :mc-seqno (cons 100 200) :lt (cons 1000 2000))))
        (check "a slice without limits covers every query"
               (cl-ton::%slice-covers-p nil (q :workchain 0 :seqno 5 :lt 5)))
        (check "inside the shard, the seqno range and the lt range: covered"
               (cl-ton::%slice-covers-p slice (q :workchain 0 :account-hash (%hash-starting #x10) :seqno 150 :lt 1500)))
        (check "another workchain is not covered"
               (not (cl-ton::%slice-covers-p slice (q :workchain -1 :account-hash (%hash-starting #x10) :seqno 150))))
        (check "an account outside the slice's shard is not covered"
               (not (cl-ton::%slice-covers-p slice (q :workchain 0 :account-hash (%hash-starting #xC0) :seqno 150))))
        (check "a query without an account is covered by shard membership of the workchain"
               (cl-ton::%slice-covers-p slice (q :workchain 0 :seqno 150)))
        (check "a seqno outside the range is not covered, the bounds are inclusive"
               (and (not (cl-ton::%slice-covers-p slice (q :workchain 0 :seqno 99)))
                    (not (cl-ton::%slice-covers-p slice (q :workchain 0 :seqno 201)))
                    (cl-ton::%slice-covers-p slice (q :workchain 0 :seqno 100))
                    (cl-ton::%slice-covers-p slice (q :workchain 0 :seqno 200))))
        (check "an lt outside the range is not covered"
               (and (not (cl-ton::%slice-covers-p slice (q :workchain 0 :lt 999)))
                    (not (cl-ton::%slice-covers-p slice (q :workchain 0 :lt 2001)))))
        (check "an open-ended range covers everything above its start"
               (cl-ton::%slice-covers-p (list :mc-seqno (cons 100 nil)) (q :seqno 99999999)))))))

(declaim (ftype function %tuple-value-cell))

(defun %value-cell (item)
  "The cell of one VmStackValue (a tuple included)."
  (if (and (consp item) (eq (car item) :tuple))
      (%tuple-value-cell (cdr item))
      (end-cell (cl-ton::store-stack-value (begin-cell) item))))

(defun %tuple-head (items)
  "The VmTupleRef of ITEMS (at least one): the value cell of a single item, else a cell with the refs head and last."
  (if (null (cdr items))
      (%value-cell (first items))
      (end-cell (store-ref (store-ref (begin-cell) (%tuple-head (butlast items)))
                           (%value-cell (car (last items)))))))

(defun %tuple-value-cell (items)
  "A VmStackValue tuple$_ cell (tag 7, 16-bit length, VmTuple) built by hand: the serializer refuses tuples."
  (let* ((len (length items))
         (b (store-uint (store-uint (begin-cell) 7 8) len 16)))
    (end-cell (case len
                (0 b)
                (1 (store-ref b (%value-cell (first items))))
                (t (store-ref (store-ref b (%tuple-head (butlast items)))
                              (%value-cell (car (last items)))))))))

(defun test-vm-tuples ()
  (format t "VM stack tuples of every size parse~%")
  (check "the serializer refuses tuples, as documented"
         (handler-case (progn (serialize-vm-stack (list (list :tuple 1))) nil)
           (cl-ton:ton-error () t)))
  (dolist (item (list '(:tuple)
                      '(:tuple 1)
                      '(:tuple 1 2)
                      '(:tuple 1 2 3)
                      '(:tuple 1 2 3 4 5)
                      '(:tuple 1 (:tuple 2 3) 4)
                      '(:tuple (:tuple) :null -7)))
    (check (format nil "~S is parsed back from its hand-built cells" item)
           (equal item (cl-ton::parse-stack-value (cell-slice (%tuple-value-cell (cdr item))))))))

(defun test-wait-for-published-head ()
  (format t "head poller: waiting for a newer published head~%")
  (flet ((head (seqno)
           (let ((z (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
             (make-block-id :workchain -1 :shard (- (expt 2 63)) :seqno seqno :root-hash z :file-hash z))))
    (let ((poller (cl-ton::%make-head-poller nil)))
      (check "nothing published: the wait times out with NIL"
             (null (cl-ton::wait-for-published-head poller nil 0.05)))
      (cl-ton::publish-head poller (head 10))
      (check "a head newer than no baseline is returned at once"
             (eql 10 (block-id-seqno (cl-ton::wait-for-published-head poller nil 0.05))))
      (check "a head not newer than the baseline times out"
             (null (cl-ton::wait-for-published-head poller 10 0.05)))
      (cl-ton::publish-head poller (head 9))
      (check "an older head never replaces the published one"
             (eql 10 (block-id-seqno (cl-ton::head-poller-head poller))))
      (let ((waiter (sb-thread:make-thread
                     (lambda () (cl-ton::wait-for-published-head poller 10 5)))))
        (sleep 0.1)
        (cl-ton::publish-head poller (head 11))
        (check "a waiter is woken by the next published head"
               (eql 11 (block-id-seqno (sb-thread:join-thread waiter :default nil :timeout 5)))))
      (let ((waiter (sb-thread:make-thread
                     (lambda () (cl-ton::wait-for-published-head poller 11 5)))))
        (sleep 0.1)
        (sb-thread:with-mutex ((cl-ton::head-poller-lock poller))
          (setf (cl-ton::head-poller-stop-p poller) t)
          (sb-thread:condition-broadcast (cl-ton::head-poller-queue poller)))
        (check "stopping the poller ends the wait with NIL"
               (null (sb-thread:join-thread waiter :default :hung :timeout 5)))))))

(defun test-scan-confirmed-flow ()
  (format t "confirmed-flow scan: shards, watched pools, once per masterchain block~%")
  (let* ((zero (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))
         (left-pool (fake-address #x11))
         (right-pool (fake-address #xF1))
         (stranger (fake-address #xF2))
         (master (make-block-id :workchain -1 :shard (- (expt 2 63)) :seqno 500 :root-hash zero :file-hash zero))
         (left-shard (make-block-id :workchain 0 :shard #x4000000000000000 :seqno 7 :root-hash zero :file-hash zero))
         (right-shard (make-block-id :workchain 0 :shard (- #x4000000000000000) :seqno 7 :root-hash zero :file-hash zero))
         (txs-of-right (list (make-short-tx-id :account (address-hash right-pool) :lt 1 :hash zero)
                             (make-short-tx-id :account (address-hash stranger) :lt 2 :hash zero)))
         (queried '()) (master-calls 0) (events '()))
    ;; the scan reaches the chain through the TONLIB-* functions; stand-ins answer them
    (sb-int:encapsulate 'cl-ton::tonlib-masterchain-block 'stage3
                        (lambda (f &rest args) (declare (ignore f args)) (incf master-calls) master))
    (sb-int:encapsulate 'cl-ton::tonlib-shards 'stage3
                        (lambda (f &rest args) (declare (ignore f args)) (list left-shard right-shard)))
    (sb-int:encapsulate 'cl-ton::tonlib-block-transactions 'stage3
                        (lambda (f tl shard &rest args)
                          (declare (ignore f tl args))
                          (push shard queried)
                          (if (eq shard right-shard) txs-of-right '())))
    (unwind-protect
         (let ((scanner (cl-ton::%make-flow-scanner nil (list right-pool))))
           (setf (cl-ton::flow-scanner-callback scanner) (lambda (e) (push e events)))
           (cl-ton::scan-confirmed-flow-once scanner)
           (check "only the shard that can hold a watched pool is read"
                  (equal (list right-shard) queried))
           (check "a transaction of a watched pool becomes an event, one of a stranger does not"
                  (let ((drained (cl-ton::drain-flow-events scanner)))
                    (and (= 1 (length drained))
                         (address-equal right-pool (cl-ton::flow-event-pool (first drained)))
                         (eq right-shard (cl-ton::flow-event-block (first drained)))
                         (eql 1 (short-tx-lt (cl-ton::flow-event-transaction (first drained)))))))
           (check "the callback got the same event"
                  (and (= 1 (length events)) (eql 1 (short-tx-lt (cl-ton::flow-event-transaction (first events))))))
           (check "the masterchain seqno is remembered"
                  (eql 500 (cl-ton::flow-scanner-last-seqno scanner)))
           (setf queried '())
           (cl-ton::scan-confirmed-flow-once scanner)
           (check "the same masterchain block is not scanned twice"
                  (and (null queried) (null (cl-ton::drain-flow-events scanner)))))
      (dolist (f '(cl-ton::tonlib-masterchain-block cl-ton::tonlib-shards cl-ton::tonlib-block-transactions))
        (sb-int:unencapsulate f 'stage3)))
    (check "the stand-ins answered the masterchain block twice (two scans)" (= 2 master-calls))))

(defun test-coverage-stage3 ()
  (test-proxy-shard-routing)
  (test-vm-tuples)
  (test-wait-for-published-head)
  (test-scan-confirmed-flow))
