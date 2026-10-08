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

;;;; slice.lisp -- immutable cursor over a cell's data bits and references.
;;;;
;;;; Every LOAD-* function returns (values VALUE NEW-SLICE); the input slice
;;;; is never modified.  This mirrors the builder discipline of TON-BOC.

(in-package :cl-ton)

(defstruct (slice (:constructor %make-slice (cell bit-pos ref-pos))
                  (:copier nil))
  (cell nil :type cell :read-only t)
  (bit-pos 0 :type (integer 0 1023) :read-only t)
  (ref-pos 0 :type (integer 0 4) :read-only t))

(defun cell-slice (cell)
  "A slice reading CELL from its first bit.  An exotic cell (pruned branch, library reference,
Merkle proof or update) is not data: its bytes are a type, a level mask and hashes, and reading
them as TL-B would let a pruned subtree pass for content -- the C++ VM's virtualization error."
  (when (cell-exotic-p cell)
    (ton-error "virtualization error: cannot read ~A as data"
               (case (cell-special-type cell)
                 (1 "a pruned branch") (2 "a library reference") (3 "a Merkle proof") (4 "a Merkle update")
                 (t "an exotic cell"))))
  (%make-slice cell 0 0))

(defun slice-remaining-bits (s)
  (- (cell-bit-length (slice-cell s)) (slice-bit-pos s)))

(defun slice-remaining-refs (s)
  (- (length (cell-refs (slice-cell s))) (slice-ref-pos s)))

(defun slice-empty-p (s)
  (and (zerop (slice-remaining-bits s)) (zerop (slice-remaining-refs s))))

(defun load-uint (s n)
  "Read N bits as an unsigned integer."
  (when (> n (slice-remaining-bits s))
    (ton-error "Slice underflow: need ~D bits, ~D left" n (slice-remaining-bits s)))
  (values (cell-uint (slice-cell s) (slice-bit-pos s) n)
          (%make-slice (slice-cell s) (+ (slice-bit-pos s) n) (slice-ref-pos s))))

(defun load-int (s n)
  "Read N bits as a two's complement integer."
  (multiple-value-bind (u s2) (load-uint s n)
    (values (if (logbitp (1- n) u) (- u (ash 1 n)) u) s2)))

(defun load-bit (s)
  (multiple-value-bind (b s2) (load-uint s 1)
    (values (= b 1) s2)))

(defun skip-bits (s n)
  (nth-value 1 (load-uint s n)))

(defun load-bytes (s nbytes)
  (multiple-value-bind (u s2) (load-uint s (* 8 nbytes))
    (values (uint->octets u nbytes) s2)))

(defun load-coins (s)
  "VarUInteger 16: 4-bit byte count followed by that many bytes."
  (multiple-value-bind (len s2) (load-uint s 4)
    (load-uint s2 (* 8 len))))

(defun load-ref (s)
  (when (zerop (slice-remaining-refs s))
    (ton-error "Slice underflow: no references left"))
  (let ((ref (aref (cell-refs (slice-cell s)) (slice-ref-pos s))))
    (unless (cell-p ref)
      (ton-error "Reference is not a full cell: ~S" ref))
    (values ref (%make-slice (slice-cell s) (slice-bit-pos s) (1+ (slice-ref-pos s))))))

(defun load-maybe-ref (s)
  "Maybe ^Cell: a presence bit, then a ref if set.  Returns (values CELL-OR-NIL SLICE)."
  (multiple-value-bind (present s2) (load-bit s)
    (if present (load-ref s2) (values nil s2))))

(defun load-address (s)
  "MsgAddress.  Returns (values ADDRESS-OR-NIL SLICE); addr_none gives NIL."
  (multiple-value-bind (tag s2) (load-uint s 2)
    (ecase tag
      (0 (values nil s2))
      (2 (multiple-value-bind (anycast s3) (load-bit s2)
           (when anycast (ton-error "Anycast addresses are not supported"))
           (multiple-value-bind (wc s4) (load-int s3 8)
             (multiple-value-bind (hash s5) (load-bytes s4 32)
               (values (make-address :workchain wc :hash hash) s5)))))
      ((1 3) (ton-error "External / var addresses are not supported (tag ~D)" tag)))))

(defun slice-rest-bits (s)
  "All remaining data bits as an unsigned integer plus their count."
  (let ((n (slice-remaining-bits s)))
    (values (cell-uint (slice-cell s) (slice-bit-pos s) n) n)))
