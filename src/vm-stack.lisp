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

;;;; vm-stack.lisp -- TVM stack values.
;;;;
;;;; A stack is a Lisp list ordered deepest-first (the order in which get
;;;; method arguments are pushed and in which results are documented).
;;;; Items are: integers, :NULL, CELLs, SLICEs, or (:TUPLE . items).
;;;;
;;;; Two encodings are supported:
;;;;   * the TL-B VmStack cell used by libemulator
;;;;   * the tonlibjson tvm.stackEntry* JSON objects

(in-package :cl-ton)

(defun stack-slice (c) (if (slice-p c) c (cell-slice c)))
(defconstant +stack-null+ :null)
(defun stack-null () :null)

;;; --- TL-B (emulator) -------------------------------------------------

(defun store-stack-value (b item)
  (cond ((eq item :null) (store-uint b 0 8))
        ((integerp item)
         (if (<= (- (ash 1 63)) item (1- (ash 1 63)))
             (store-int (store-uint b 1 8) item 64)
             (store-int (store-uint b #x100 15) item 257)))
        ((cell-p item) (store-ref (store-uint b 3 8) item))
        ((slice-p item)
         (let* ((c (slice-cell item))
                (b (store-ref (store-uint b 4 8) c))
                (b (store-uint b (slice-bit-pos item) 10))
                (b (store-uint b (cell-bit-length c) 10))
                (b (store-uint b (slice-ref-pos item) 3)))
           (store-uint b (length (cell-refs c)) 3)))
        ((and (consp item) (eq (car item) :tuple))
         (ton-error "Serializing tuples onto the stack is not supported"))
        (t (ton-error "Unknown stack item ~S" item))))

(defun stack-list-cell (items)
  "VmStackList for ITEMS (deepest first): each cell = ^rest tos."
  (if (null items)
      (end-cell (begin-cell))
      (let ((rest (stack-list-cell (butlast items))))
        (end-cell (store-stack-value (store-ref (begin-cell) rest) (car (last items)))))))

(defun serialize-vm-stack (items)
  "vm_stack#_ depth:(## 24) stack:(VmStackList depth) as a cell."
  (let ((b (store-uint (begin-cell) (length items) 24)))
    (if (null items)
        (end-cell b)
        (let ((list-cell (stack-list-cell items)))
          ;; The list's top cons is inlined into the vm_stack cell.
          (end-cell (store-builder b (cell->builder list-cell)))))))

(defun parse-stack-value (s)
  "Returns (values ITEM SLICE)."
  (multiple-value-bind (tag s) (load-uint s 8)
    (case tag
      (0 (values :null s))
      (1 (load-int s 64))
      (2 (multiple-value-bind (sub s) (load-uint s 7)
           (if (= sub #b1111111)
               (multiple-value-bind (_ s) (load-uint s 1)
                 (declare (ignore _))
                 (values :nan s))
               (progn
                 (unless (zerop sub) (ton-error "Bad vm_stk_int tag"))
                 (load-int s 257)))))
      (3 (load-ref s))
      (4 (multiple-value-bind (c s) (load-ref s)
           (multiple-value-bind (st-bits s) (load-uint s 10)
             (multiple-value-bind (end-bits s) (load-uint s 10)
               (multiple-value-bind (st-ref s) (load-uint s 3)
                 (multiple-value-bind (end-ref s) (load-uint s 3)
                   ;; Trim the cell to [st,end) by rebuilding it; keeps the
                   ;; slice self-contained.
                   (let ((trimmed (end-cell
                                   (reduce #'store-ref
                                           (subseq (coerce (cell-refs c) 'list) st-ref end-ref)
                                           :initial-value
                                           (store-bits (begin-cell)
                                                       (cell-uint c st-bits (- end-bits st-bits))
                                                       (- end-bits st-bits))))))
                     (values (cell-slice trimmed) s))))))))
      (5 (load-ref s))
      (7 (multiple-value-bind (len s) (load-uint s 16)
           (values (cons :tuple (parse-vm-tuple s len)) (skip-tuple-refs s len))))
      (t (ton-error "Unsupported VmStackValue tag ~D" tag)))))

(defun skip-tuple-refs (s len)
  (case len (0 s) (1 (nth-value 1 (load-ref s))) (t (nth-value 1 (load-ref (nth-value 1 (load-ref s)))))))

(defun parse-vm-tuple (s len)
  "VmTuple len: head:(VmTupleRef n) tail:^VmStackValue."
  (case len
    (0 '())
    (1 (list (parse-stack-value (cell-slice (load-ref s)))))
    (t (multiple-value-bind (head-ref s2) (load-ref s)
         (let ((head (if (= len 2)
                         (list (parse-stack-value (cell-slice head-ref)))
                         (parse-vm-tuple (cell-slice head-ref) (1- len)))))
           (append head (list (parse-stack-value (cell-slice (load-ref s2))))))))))

(defun parse-vm-stack (cell)
  "Inverse of SERIALIZE-VM-STACK; returns the deepest-first item list."
  (let ((s (cell-slice cell)))
    (multiple-value-bind (depth s) (load-uint s 24)
      (labels ((walk (s n)
                 (if (zerop n)
                     '()
                     (multiple-value-bind (rest s) (load-ref s)
                       (let ((tos (parse-stack-value s)))
                         (append (walk (cell-slice rest) (1- n)) (list tos)))))))
        (walk s depth)))))

;;; --- tonlibjson JSON -------------------------------------------------

(defun stack-item->json (item)
  (cond ((eq item :null)
         (ton-error "tonlib cannot pass null stack entries"))
        ((integerp item)
         (list :|@type| "tvm.stackEntryNumber"
               :|number| (list :|@type| "tvm.numberDecimal" :|number| (format nil "~D" item))))
        ((cell-p item)
         (list :|@type| "tvm.stackEntryCell"
               :|cell| (list :|@type| "tvm.cell" :|bytes| (cell->base64 item))))
        ((slice-p item)
         (unless (and (zerop (slice-bit-pos item)) (zerop (slice-ref-pos item)))
           (ton-error "tonlib slices must start at the cell beginning"))
         (list :|@type| "tvm.stackEntrySlice"
               :|slice| (list :|@type| "tvm.slice" :|bytes| (cell->base64 (slice-cell item)))))
        (t (ton-error "Cannot encode stack item ~S for tonlib" item))))

(defun json-get (obj &rest keys)
  "Nested lookup in a Jonathan hash-table document."
  (reduce (lambda (o k) (and (hash-table-p o) (gethash k o))) keys :initial-value obj))

(defun json->stack-item (entry)
  (let ((type (json-get entry "@type")))
    (cond ((equal type "tvm.stackEntryNumber")
           (parse-integer (json-get entry "number" "number")))
          ((equal type "tvm.stackEntryCell")
           (base64->cell (json-get entry "cell" "bytes")))
          ((equal type "tvm.stackEntrySlice")
           (cell-slice (base64->cell (json-get entry "slice" "bytes"))))
          ((member type '("tvm.stackEntryTuple" "tvm.stackEntryList") :test #'equal)
           (cons :tuple (mapcar #'json->stack-item
                                (json-get entry (if (equal type "tvm.stackEntryTuple") "tuple" "list")
                                          "elements"))))
          (t (ton-error "Unsupported tonlib stack entry ~S" type)))))
