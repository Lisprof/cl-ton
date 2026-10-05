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

;;;; types.lisp -- TL-B building blocks used by wallet and DEX messages:
;;;; MsgAddress, Coins, Maybe/Either refs, StateInit, message envelopes.
;;;;
;;;; All STORE-* functions follow the TON-BOC convention: they take a
;;;; builder and return a new builder.

(in-package :cl-ton)

;;; ---------------------------------------------------------------------
;;; Addresses
;;; ---------------------------------------------------------------------

(defstruct (address (:copier nil))
  (workchain 0 :type (integer -128 127) :read-only t)
  (hash (octets) :type octets :read-only t))

(defun address-equal (a b)
  (and (address-p a) (address-p b)
       (= (address-workchain a) (address-workchain b))
       (equalp (address-hash a) (address-hash b))))

(defun crc16-xmodem (octets)
  "CRC-16/XMODEM (poly 0x1021, init 0), as used by user-friendly addresses
and TVM method ids."
  (let ((crc 0))
    (loop for b across (as-octets octets)
          do (setf crc (logxor crc (ash b 8)))
             (loop repeat 8
                   do (setf crc (if (logbitp 15 crc)
                                    (logand #xffff (logxor (ash crc 1) #x1021))
                                    (logand #xffff (ash crc 1))))))
    crc))

(defun address->string (addr &key (bounceable t) testnet (url t))
  "User-friendly 48-character form (base64url by default)."
  (let* ((tag (logior (if bounceable #x11 #x51) (if testnet #x80 0)))
         (body (concat-octets (list (octets tag (logand #xff (address-workchain addr)))
                                    (address-hash addr))))
         (crc (crc16-xmodem body)))
    (base64-encode (concat-octets (list body (uint->octets crc 2))) :url url)))

(defun address->raw-string (addr)
  (format nil "~D:~A" (address-workchain addr) (octets->hex (address-hash addr))))

(defun parse-address (string)
  "Accept raw (\"0:hex\") or user-friendly (base64/base64url) addresses.
Returns (values ADDRESS BOUNCEABLE-P TESTNET-P); raw addresses report T NIL."
  (let ((colon (position #\: string)))
    (if colon
        (let ((wc (parse-integer string :end colon))
              (hash (hex->octets (subseq string (1+ colon)))))
          (unless (= 32 (length hash))
            (ton-error "Raw address hash must be 32 bytes: ~S" string))
          (values (make-address :workchain wc :hash hash) t nil))
        (let ((bytes (base64-decode string)))
          (unless (= 36 (length bytes))
            (ton-error "User-friendly address must decode to 36 bytes: ~S" string))
          (let* ((tag (aref bytes 0))
                 (testnet (logbitp 7 tag))
                 (tag (logand tag #x7f))
                 (wc (let ((b (aref bytes 1))) (if (> b 127) (- b 256) b)))
                 (crc (octets->uint bytes :start 34 :end 36)))
            (unless (member tag '(#x11 #x51))
              (ton-error "Unknown address tag #x~2,'0x in ~S" tag string))
            (unless (= crc (crc16-xmodem (subseq bytes 0 34)))
              (ton-error "Address checksum mismatch: ~S" string))
            (values (make-address :workchain wc :hash (subseq bytes 2 34))
                    (= tag #x11) testnet))))))

(defmethod print-object ((a address) stream)
  (print-unreadable-object (a stream :type t)
    (write-string (address->string a) stream)))

(defun store-address (b addr)
  "MsgAddress: addr_none$00 when ADDR is NIL, else addr_std$10 without anycast."
  (if (null addr)
      (store-uint b 0 2)
      (let ((b (store-uint b #b100 3)))
        (store-bytes (store-int b (address-workchain addr) 8) (address-hash addr)))))

;;; ---------------------------------------------------------------------
;;; Coins and unit helpers
;;; ---------------------------------------------------------------------

(defun store-var-uint (b value len-bits)
  (unless (and (integerp value) (>= value 0))
    (ton-error "VarUInteger must be a non-negative integer: ~S" value))
  (let ((nbytes (if (zerop value) 0 (ceiling (integer-length value) 8))))
    (when (>= nbytes (ash 1 len-bits))
      (ton-error "Value ~D too large for VarUInteger ~D" value len-bits))
    (store-uint (store-uint b nbytes len-bits) value (* 8 nbytes))))

(defun store-coins (b nanotons)
  "Grams / Coins = VarUInteger 16."
  (store-var-uint b nanotons 4))

(defun store-maybe-ref (b cell)
  (if cell (store-ref (store-bit b 1) cell) (store-bit b 0)))

(defun store-either-ref (b cell)
  "Either X ^X, always taking the ^X branch."
  (store-ref (store-bit b 1) cell))

(defun store-string-tail (b string)
  (store-bytes b (sb-ext:string-to-octets string :external-format :utf-8)))

(defun nano (ton)
  "TON (rational or float) -> nanoTON integer."
  (values (round (* (rational ton) 1000000000))))

(defun from-nano (nanotons)
  (/ nanotons 1000000000))

(defun usdt-units (usdt)
  "USDT (6 decimals) -> jetton base units."
  (values (round (* (rational usdt) 1000000))))

(defun from-usdt-units (units)
  (/ units 1000000))

;;; ---------------------------------------------------------------------
;;; Hashmap (dictionary) serialization
;;;
;;; Enough of TL-B Hashmap to build small dictionaries such as the
;;; library collection handed to the emulator.  ENTRIES is a list of
;;; (KEY-INTEGER . VALUE-STORER) where VALUE-STORER is a function from
;;; builder to builder.
;;; ---------------------------------------------------------------------

(defun store-hm-label (b label-bits label-length max-length)
  "HmLabel ~len max: pick the shortest of hml_short / hml_long / hml_same."
  (let* ((n label-length)
         (m max-length)
         (len-bits (integer-length m))
         (same (and (plusp n)
                    (or (zerop label-bits) (= label-bits (1- (ash 1 n))))))
         (short-size (+ 1 (1+ n) n))
         (long-size (+ 2 len-bits n))
         (same-size (+ 2 1 len-bits)))
    (cond ((and same (< same-size (min short-size long-size)))
           (let ((b (store-uint b #b11 2)))
             (store-uint (store-bit b (if (zerop label-bits) 0 1)) n len-bits)))
          ((<= short-size long-size)
           (let* ((b (store-bit b 0))
                  (b (store-uint b (1- (ash 1 n)) n))   ; Unary ~n: n ones ...
                  (b (store-bit b 0)))                  ; ... then a zero
             (store-uint b label-bits n)))
          (t
           (let ((b (store-uint b #b10 2)))
             (store-uint (store-uint b n len-bits) label-bits n))))))

(defun hashmap-cell (entries key-length)
  "Hashmap KEY-LENGTH X for a non-empty list of (KEY . STORER)."
  (labels ((build (entries n)
             ;; Common prefix of all keys within the remaining N bits.
             (let* ((first-key (car (first entries)))
                    (prefix-len
                      (loop for l from 0 below n
                            while (every (lambda (e)
                                           (= (ldb (byte 1 (- n l 1)) (car e))
                                              (ldb (byte 1 (- n l 1)) first-key)))
                                         entries)
                            count t))
                    (label (ldb (byte prefix-len (- n prefix-len)) first-key))
                    (b (store-hm-label (begin-cell) label prefix-len n))
                    (m (- n prefix-len)))
               (if (zerop m)
                   (end-cell (funcall (cdr (first entries)) b))
                   (let* ((bit (1- m))
                          (left (remove-if (lambda (e) (logbitp bit (car e))) entries))
                          (right (remove-if-not (lambda (e) (logbitp bit (car e))) entries)))
                     (end-cell (store-ref (store-ref b (build left (1- m)))
                                          (build right (1- m)))))))))
    (when (null entries) (ton-error "Hashmap needs at least one entry"))
    (build entries key-length)))

(defun store-dict (b entries key-length)
  "HashmapE KEY-LENGTH X: hme_empty$0 or hme_root$1 ^Hashmap."
  (if (null entries)
      (store-bit b 0)
      (store-ref (store-bit b 1) (hashmap-cell entries key-length))))

;;; ---------------------------------------------------------------------
;;; StateInit and contract addresses
;;; ---------------------------------------------------------------------

(defun make-state-init (code data)
  "_ split_depth:(Maybe (## 5)) special:(Maybe TickTock)
     code:(Maybe ^Cell) data:(Maybe ^Cell) library:(HashmapE 256 SimpleLib)"
  (build-cell (store-bit 0) (store-bit 0)
              (store-maybe-ref code) (store-maybe-ref data)
              (store-bit 0)))

(defun state-init-address (state-init &key (workchain 0))
  (make-address :workchain workchain :hash (cell-hash state-init)))

;;; ---------------------------------------------------------------------
;;; Message envelopes
;;; ---------------------------------------------------------------------

(defstruct (message-spec (:copier nil))
  "What the wallet should send: an internal message destination, value and body."
  (to nil :read-only t)                         ; address
  (value 0 :type integer :read-only t)          ; nanoTON attached
  (body nil :read-only t)                       ; cell
  (bounce t :read-only t)
  (state-init nil :read-only t))                ; cell or nil: deploys DEST with the message

(defun message-spec->relaxed (spec)
  (internal-message-relaxed :to (message-spec-to spec) :value (message-spec-value spec)
                            :body (message-spec-body spec) :bounce (message-spec-bounce spec)
                            :state-init (message-spec-state-init spec)))

(defun cell->builder (cell)
  (reduce #'store-ref (coerce (cell-refs cell) 'list)
          :initial-value (store-bits (begin-cell) (cell-bits cell) (cell-bit-length cell))))

(defun store-message-init (b state-init)
  "init:(Maybe (Either StateInit ^StateInit)), inlined when it fits
(same rule as @ton/core so serialisations match byte for byte)."
  (cond ((null state-init) (store-bit b 0))
        ((>= (- 1023 (builder-bit-length b) 2) (cell-bit-length state-init))
         (store-builder (store-uint b #b10 2) (cell->builder state-init)))
        (t (store-ref (store-uint b #b11 2) state-init))))

(defun store-message-body (b body)
  "body:(Either X ^X), inlined when bits and refs fit (as @ton/core does)."
  (cond ((null body) (store-bit b 0))
        ((and (>= (- 1023 (builder-bit-length b) 1) (cell-bit-length body))
              (<= (+ (length (builder-refs b)) (length (cell-refs body))) 4)
              (not (cell-exotic-p body)))
         (store-builder (store-bit b 0) (cell->builder body)))
        (t (store-ref (store-bit b 1) body))))

(defun internal-message-relaxed (&key to value body (bounce t) state-init)
  "MessageRelaxed with int_msg_info, src = addr_none, fees/lt/time zero
(the wallet fills them in)."
  (let* ((b (begin-cell))
         (b (store-uint b 0 1))                 ; int_msg_info$0
         (b (store-bit b 1))                    ; ihr_disabled
         (b (store-bit b bounce))               ; bounce
         (b (store-bit b 0))                    ; bounced
         (b (store-address b nil))              ; src
         (b (store-address b to))               ; dest
         (b (store-coins b value))              ; value.grams
         (b (store-bit b 0))                    ; value.other = empty dict
         (b (store-coins b 0))                  ; ihr_fee
         (b (store-coins b 0))                  ; fwd_fee
         (b (store-uint b 0 64))                ; created_lt
         (b (store-uint b 0 32))                ; created_at
         (b (store-message-init b state-init))
         (b (store-message-body b body)))
    (end-cell b)))

(defun external-message (&key to body state-init)
  "Message with ext_in_msg_info, src = addr_none, import_fee 0."
  (let* ((b (begin-cell))
         (b (store-uint b #b10 2))              ; ext_in_msg_info$10
         (b (store-address b nil))              ; src
         (b (store-address b to))               ; dest
         (b (store-coins b 0))                  ; import_fee
         (b (store-message-init b state-init))
         (b (store-message-body b body)))
    (end-cell b)))
