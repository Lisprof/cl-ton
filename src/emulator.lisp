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

;;;; emulator.lisp -- CFFI binding to libemulator.
;;;;
;;;; Two entry points:
;;;;   RUN-GET-METHOD-LOCAL      run a getter on code+data fetched earlier
;;;;   EMULATE-EXTERNAL-MESSAGE  dry-run a signed external message against
;;;;                             the wallet's ShardAccount and the config
;;;; Both return plain Lisp values; native handles never escape.

(in-package :cl-ton)

(cffi:define-foreign-library libemulator
  (:unix (:or "../lib/libemulator-linux-x86_64.so"))
  (t (:default "libemulator")))

(cffi:defcfun ("emulator_set_verbosity_level" %em-set-verbosity) :bool (level :int))
(cffi:defcfun ("emulator_version" %em-version) :pointer)

(cffi:defcfun ("tvm_emulator_create" %tvm-create) :pointer
  (code :string) (data :string) (vm-log-verbosity :int))
(cffi:defcfun ("tvm_emulator_destroy" %tvm-destroy) :void (em :pointer))
(cffi:defcfun ("tvm_emulator_set_libraries" %tvm-set-libraries) :bool (em :pointer) (libs :string))
(cffi:defcfun ("tvm_emulator_set_c7" %tvm-set-c7) :bool
  (em :pointer) (address :string) (unixtime :uint32) (balance :uint64)
  (rand-seed-hex :string) (config :pointer))
(cffi:defcfun ("tvm_emulator_set_gas_limit" %tvm-set-gas-limit) :bool (em :pointer) (limit :int64))
(cffi:defcfun ("tvm_emulator_run_get_method" %tvm-run-get-method) :pointer
  (em :pointer) (method-id :int) (stack :string))

(cffi:defcfun ("transaction_emulator_create" %tx-create) :pointer
  (config :string) (vm-log-verbosity :int))
(cffi:defcfun ("transaction_emulator_destroy" %tx-destroy) :void (em :pointer))
(cffi:defcfun ("transaction_emulator_set_unixtime" %tx-set-unixtime) :bool (em :pointer) (unixtime :uint32))
(cffi:defcfun ("transaction_emulator_set_lt" %tx-set-lt) :bool (em :pointer) (lt :uint64))
(cffi:defcfun ("transaction_emulator_set_rand_seed" %tx-set-rand-seed) :bool (em :pointer) (seed-hex :string))
(cffi:defcfun ("transaction_emulator_set_libs" %tx-set-libs) :bool (em :pointer) (libs :string))
(cffi:defcfun ("transaction_emulator_set_ignore_chksig" %tx-set-ignore-chksig) :bool (em :pointer) (ignore :bool))
(cffi:defcfun ("transaction_emulator_emulate_transaction" %tx-emulate) :pointer
  (em :pointer) (shard-account :string) (message :string))

(cffi:defcfun ("free" %c-free) :void (ptr :pointer))

(defvar *emulator-loaded* nil)

(defun load-emulator-library (&optional path)
  (unless *emulator-loaded*
    (if path
        (cffi:load-foreign-library path)
        (cffi:use-foreign-library libemulator))
    (%em-set-verbosity 0)
    (setf *emulator-loaded* t)))

(defun take-c-string (ptr)
  "Convert a malloc'd C string to Lisp and free it."
  (if (cffi:null-pointer-p ptr)
      nil
      (unwind-protect (cffi:foreign-string-to-lisp ptr)
        (%c-free ptr))))

(defun emulator-version ()
  (load-emulator-library)
  (take-c-string (%em-version)))

(defun method-id (name)
  "TVM get-method id: (crc16-xmodem(name) & 0xffff) | 0x10000."
  (logior (crc16-xmodem (sb-ext:string-to-octets name :external-format :utf-8)) #x10000))

(defun libraries-dict-cell (libraries)
  "HashmapE 256 ^Cell from an alist of (hash-hex . cell); NIL when empty."
  (and libraries
       (hashmap-cell (mapcar (lambda (entry)
                               (cons (parse-integer (car entry) :radix 16)
                                     (let ((cell (cdr entry)))
                                       (lambda (b) (store-ref b cell)))))
                             libraries)
                     256)))

(defun unix-now ()
  (- (get-universal-time) #.(encode-universal-time 0 0 0 1 1 1970 0)))

(defun run-get-method-local (code data method stack
                             &key address (balance 1000000000) config libraries
                                  (unixtime (unix-now)) (gas-limit 1000000))
  "Run getter METHOD on CODE/DATA cells with STACK (deepest first) inside
libemulator.  Returns (values ITEMS EXIT-CODE GAS-USED MISSING-LIBRARY-HEX)."
  (load-emulator-library)
  (let ((em (%tvm-create (cell->base64 code) (cell->base64 data) 0)))
    (when (cffi:null-pointer-p em) (error 'emulator-error :format-control "tvm_emulator_create failed"))
    (unwind-protect
         (progn
           (when libraries
             (%tvm-set-libraries em (cell->base64 (libraries-dict-cell libraries))))
           (%tvm-set-gas-limit em gas-limit)
           (let ((rand-seed (octets->hex (sha256 (uint->octets (get-internal-real-time) 8)))))
             (if config
                 (cffi:with-foreign-string (cfg (cell->base64 config))
                   (%tvm-set-c7 em (address->string (or address (make-address)))
                                unixtime balance rand-seed cfg))
                 (%tvm-set-c7 em (address->string (or address (make-address)))
                              unixtime balance rand-seed (cffi:null-pointer))))
           (let* ((raw (take-c-string
                        (%tvm-run-get-method em (if (integerp method) method (method-id method))
                                             (cell->base64 (serialize-vm-stack stack)))))
                  (r (json-decode raw)))
             (unless (json-get r "success")
               (error 'emulator-error :format-control "run_get_method failed: ~A"
                                      :format-arguments (list (json-get r "error"))))
             (let ((missing (json-get r "missing_library")))
               (values (parse-vm-stack (base64->cell (json-get r "stack")))
                       (json-get r "vm_exit_code")
                       (let ((g (json-get r "gas_used"))) (if (stringp g) (parse-integer g) g))
                       (and missing (stringp missing) missing)))))
      (%tvm-destroy em))))

(defun run-account-get-method (account-cell method stack &key config libraries unixtime gas-limit)
  "Run getter METHOD with STACK (deepest first) on the code and data of ACCOUNT-CELL, an Account cell
(the verified one VERIFY-ACCOUNT-STATE returns): the address and balance of c7 come from the account
too, and its own libraries join LIBRARIES (an alist of (hash-hex . cell), which win).  The values of
RUN-GET-METHOD-LOCAL.  An account that is not active has nothing to run."
  (let ((account (parse-account account-cell)))
    (unless (and (eq (getf account :status) :active) (getf account :code) (getf account :data))
      (error 'emulator-error :format-control "cannot run ~A on ~A: the account is ~(~A~)~:[~; without code or data~]"
                             :format-arguments (list method
                                                     (let ((a (getf account :address))) (if a (address->string a) "?"))
                                                     (getf account :status) (eq (getf account :status) :active))))
    (let ((own (and (getf account :library-root)
                    (mapcar (lambda (entry)
                              (cons (octets->hex (uint->octets (car entry) 32)) (cdr entry)))
                            (dict-entries (getf account :library-root) 256
                                          (lambda (s) (load-ref (skip-bits s 1))))))))
      (apply #'run-get-method-local (getf account :code) (getf account :data) method stack
             :address (getf account :address) :balance (getf account :balance)
             :libraries (append libraries (remove-if (lambda (e) (assoc (car e) libraries :test #'string-equal)) own))
             (append (and config (list :config config)) (and unixtime (list :unixtime unixtime))
                     (and gas-limit (list :gas-limit gas-limit)))))))

(defstruct (emulation-result (:copier nil))
  (success-p nil :read-only t)
  (error nil :read-only t)
  (exit-code nil :read-only t)
  (fees 0 :read-only t)           ; total_fees from the emulated transaction, nanoTON
  (out-messages 0 :read-only t)
  (vm-log "" :read-only t)
  (transaction nil :read-only t)  ; cell
  (shard-account nil :read-only t))

(defun parse-transaction-summary (tx)
  "Returns (values TOTAL-FEES OUT-MSG-COUNT) from a Transaction cell."
  (let ((s (cell-slice tx)))
    (multiple-value-bind (tag s) (load-uint s 4)
      (unless (= tag #b0111) (ton-error "Not a transaction cell"))
      (let ((s (skip-bits s (+ 256 64 256 64 32))))       ; addr lt prev_hash prev_lt now
        (multiple-value-bind (outmsg-cnt s) (load-uint s 15)
          (let ((s (skip-bits s 4)))                       ; orig_status end_status
            (multiple-value-bind (_ s) (load-ref s)        ; ^[in_msg out_msgs]
              (declare (ignore _))
              (values (load-coins s) outmsg-cnt))))))))

;;; --- reading a transaction's messages -------------------------------------
;;;
;;; The emulator only reports an out-message COUNT; the cycle work needs to
;;; know WHERE the wallet's single outgoing message goes and with what body
;;; (tests assert it, and the cascade emulator below follows it), so these
;;; decode just enough TL-B to read a Transaction's out_msgs and an
;;; internal/external Message's envelope.

(defun load-hm-label (s m)
  "HmLabel ~n m.  Returns (values LABEL-BITS-AS-INTEGER N SLICE)."
  (multiple-value-bind (b0 s1) (load-uint s 1)
    (if (zerop b0)
        (let ((n 0) (cur s1))                       ; hml_short$0: unary length
          (loop (multiple-value-bind (bit next) (load-uint cur 1)
                  (setf cur next)
                  (if (= bit 1) (incf n) (return))))
          (multiple-value-bind (label s3) (load-uint cur n) (values label n s3)))
        (multiple-value-bind (b1 s2) (load-uint s1 1)
          (let ((len-bits (integer-length m)))      ; #<= m takes ceil(log2(m+1)) bits
            (if (zerop b1)
                (multiple-value-bind (n s3) (load-uint s2 len-bits) ; hml_long$10
                  (multiple-value-bind (label s4) (load-uint s3 n) (values label n s4)))
                (multiple-value-bind (v s3) (load-uint s2 1)         ; hml_same$11
                  (multiple-value-bind (n s4) (load-uint s3 len-bits)
                    (values (if (= v 1) (1- (ash 1 n)) 0) n s4)))))))))

(defun dict-entries (root key-bits value-fn)
  "Every (KEY . (funcall VALUE-FN slice-after-label)) of the Hashmap whose
root cell is ROOT, in ascending key order."
  (labels ((walk (cell m prefix)
             (multiple-value-bind (label n s) (load-hm-label (cell-slice cell) m)
               (let ((prefix (logior (ash prefix n) label))
                     (left-over (- m n)))
                 (if (zerop left-over)
                     (list (cons prefix (funcall value-fn s)))
                     (multiple-value-bind (left s2) (load-ref s)
                       (let ((right (load-ref s2)))
                         (append (walk left (1- left-over) (ash prefix 1))
                                 (walk right (1- left-over) (logior (ash prefix 1) 1))))))))))
    (walk root key-bits 0)))

(defun transaction-messages (tx)
  "(values IN-MSG-CELL-OR-NIL OUT-MSG-CELLS) of a Transaction cell."
  (let ((s (cell-slice tx)))
    (multiple-value-bind (tag s) (load-uint s 4)
      (unless (= tag #b0111) (ton-error "Not a transaction cell"))
      (let ((s (skip-bits s (+ 256 64 256 64 32))))
        (let ((s (skip-bits (nth-value 1 (load-uint s 15)) 4)))
          (let ((io (load-ref s)))
            (multiple-value-bind (in s1) (load-maybe-ref (cell-slice io))
              (multiple-value-bind (has-out s2) (load-bit s1)
                (values in
                        (and has-out
                             (mapcar #'cdr (dict-entries (load-ref s2) 15
                                                         (lambda (v) (values (load-ref v)))))))))))))))

(defun cell-from-slice-rest (s)
  "A fresh cell holding everything S has left (bits and refs)."
  (let ((b (multiple-value-bind (bits n) (slice-rest-bits s) (store-bits (begin-cell) bits n))))
    (loop while (plusp (slice-remaining-refs s))
          do (multiple-value-bind (ref next) (load-ref s) (setf b (store-ref b ref) s next)))
    (end-cell b)))

(defun parse-message-summary (msg)
  "Envelope of a Message cell as a plist: :TYPE (:INTERNAL or :EXTERNAL-IN),
:SRC :DEST (addresses or NIL), :VALUE (nanoTON, internal only), :BOUNCE and
:BODY (a cell; the body is unwrapped from its Either).  A message carrying
a StateInit is rejected -- nothing the cycle work emits or reads has one."
  (let ((s (cell-slice msg)))
    (multiple-value-bind (tag s) (load-uint s 1)
      (if (zerop tag)
          (multiple-value-bind (flags s) (load-uint s 3)            ; ihr_disabled bounce bounced
            (multiple-value-bind (src s) (load-address s)
              (multiple-value-bind (dest s) (load-address s)
                (multiple-value-bind (value s) (load-coins s)
                  (let* ((s (skip-bits s 1))                         ; no extra currencies
                         (s (nth-value 1 (load-coins s)))            ; ihr_fee
                         (s (nth-value 1 (load-coins s)))            ; fwd_fee
                         (s (skip-bits s (+ 64 32))))                ; created_lt created_at
                    (multiple-value-bind (body) (message-body-of s)
                      (list :type :internal :src src :dest dest :value value
                            :bounce (logbitp 1 flags) :body body)))))))
          (multiple-value-bind (tag2 s) (load-uint s 1)
            (unless (= tag2 0)                       ; ext_in_msg_info$10; $11 is ext_out
              (ton-error "Only internal and external-in messages are supported"))
            (multiple-value-bind (src s) (load-address s)
              (multiple-value-bind (dest s) (load-address s)
                (let ((s (nth-value 1 (load-coins s))))              ; import_fee
                  (list :type :external-in :src src :dest dest :body (message-body-of s))))))))))

(defun message-body-of (s)
  "Unwrap init:(Maybe ...) (must be absent) and body:(Either X ^X) from S."
  (multiple-value-bind (has-init s) (load-bit s)
    (when has-init (ton-error "Messages with a StateInit are not supported here"))
    (multiple-value-bind (in-ref s) (load-bit s)
      (if in-ref (values (load-ref s)) (cell-from-slice-rest s)))))

(defun parse-message-header (msg)
  "Envelope of ANY Message cell without looking at its init/body, so messages
carrying a StateInit or a big body still route.  Plist: :TYPE (:INTERNAL,
:EXTERNAL-IN or :EXTERNAL-OUT), :SRC, :DEST, and for internal messages :VALUE,
:BOUNCE, :BOUNCED."
  (let ((s (cell-slice msg)))
    (multiple-value-bind (tag s) (load-uint s 1)
      (if (zerop tag)
          (multiple-value-bind (flags s) (load-uint s 3)
            (multiple-value-bind (src s) (load-address s)
              (multiple-value-bind (dest s) (load-address s)
                (let ((value (load-coins s)))
                  (list :type :internal :src src :dest dest :value value
                        :bounce (logbitp 1 flags) :bounced (logbitp 0 flags))))))
          (multiple-value-bind (tag2 s) (load-uint s 1)
            (multiple-value-bind (src s) (load-address s)
              (multiple-value-bind (dest) (load-address s)
                (list :type (if (zerop tag2) :external-in :external-out)
                      :src src :dest dest))))))))

(defun emulation-out-message-cells (result)
  "Message cells the emulated transaction sent (NIL when it failed)."
  (and (emulation-result-transaction result)
       (nth-value 1 (transaction-messages (emulation-result-transaction result)))))

(defun emulation-out-messages-summary (result)
  "PARSE-MESSAGE-SUMMARY of each of RESULT's outgoing messages."
  (mapcar #'parse-message-summary (emulation-out-message-cells result)))

(defun emulate-external-message (config shard-account message
                                 &key libraries (unixtime (unix-now)) ignore-chksig lt rand-seed)
  "Dry-run MESSAGE against SHARD-ACCOUNT under CONFIG, both cells from tonlib.
Despite the name, libemulator takes external AND internal messages here;
EMULATE-MESSAGE is the same function.  LT pins the transaction's logical
time and RAND-SEED (64 hex chars) the TVM random seed.  Never touches the
network."
  (load-emulator-library)
  (let ((em (%tx-create (cell->base64 config) 0)))
    (when (cffi:null-pointer-p em) (error 'emulator-error :format-control "transaction_emulator_create failed"))
    (unwind-protect
         (progn
           (%tx-set-unixtime em unixtime)
           (%tx-set-ignore-chksig em (and ignore-chksig t))
           (when lt (%tx-set-lt em lt))
           (when rand-seed (%tx-set-rand-seed em rand-seed))
           (when libraries
             (%tx-set-libs em (cell->base64 (libraries-dict-cell libraries))))
           (let* ((raw (take-c-string (%tx-emulate em (cell->base64 shard-account) (cell->base64 message))))
                  (r (json-decode raw)))
             (if (json-get r "success")
                 (let ((tx (base64->cell (json-get r "transaction"))))
                   (multiple-value-bind (fees out-count) (parse-transaction-summary tx)
                     (make-emulation-result :success-p t :fees fees :out-messages out-count
                                            :vm-log (or (json-get r "vm_log") "")
                                            :transaction tx
                                            :shard-account (base64->cell (json-get r "shard_account")))))
                 (make-emulation-result :success-p nil
                                        :error (json-get r "error")
                                        :exit-code (json-get r "vm_exit_code")
                                        :vm-log (or (json-get r "vm_log") "")))))
      (%tx-destroy em))))

(defun emulate-message (config shard-account message &rest keys)
  "Emulate an internal or external MESSAGE; see EMULATE-EXTERNAL-MESSAGE."
  (apply #'emulate-external-message config shard-account message keys))

(defun funded-shard-account (addr state-init balance)
  "ShardAccount for an active account with STATE-INIT and BALANCE (nanoTON),
used to dry-run a message against a wallet that is not funded yet:
   account_descr$_ account:^Account last_trans_hash:bits256 last_trans_lt:uint64
   account$1 addr storage_stat:StorageInfo storage:AccountStorage
   storage_info$_ used:StorageUsed storage_extra:StorageExtraInfo last_paid:uint32 due_payment:(Maybe Grams)
   storage_used$_ cells:(VarUInteger 7) bits:(VarUInteger 7)
   account_storage$_ last_trans_lt:uint64 balance:CurrencyCollection state:AccountState
   account_active$1 _:StateInit"
  (let* ((account (let* ((b (store-bit (begin-cell) 1))
                         (b (store-address b addr))
                         (b (store-var-uint b 20 3))     ; cells
                         (b (store-var-uint b 5000 3))   ; bits
                         (b (store-uint b 0 3))          ; storage_extra_none
                         (b (store-uint b (unix-now) 32)) ; last_paid
                         (b (store-bit b 0))             ; due_payment none
                         (b (store-uint b 0 64))         ; last_trans_lt
                         (b (store-coins b balance))
                         (b (store-bit b 0))             ; extra currencies
                         (b (store-bit b 1))             ; account_active
                         (b (store-builder b (cell->builder state-init))))
                    (end-cell b))))
    (build-cell (store-ref account) (store-uint 0 256) (store-uint 0 64))))
