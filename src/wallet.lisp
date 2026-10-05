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

;;;; wallet.lisp -- Wallet V5R1: key derivation, address, signed external
;;;; messages.
;;;;
;;;; Keys live only inside KEYPAIR structs; PRINT-OBJECT hides them and
;;;; nothing here logs or serializes secret material.

(in-package :cl-ton)

;;; --- keys --------------------------------------------------------------

(defstruct (keypair (:constructor %make-keypair (secret public)) (:copier nil))
  (secret nil :read-only t)   ; 32-byte ed25519 seed (octets)
  (public nil :read-only t))  ; 32-byte public key (octets)

(defmethod print-object ((k keypair) stream)
  (print-unreadable-object (k stream :type t)
    (format stream "pub ~A..." (subseq (octets->hex (keypair-public k)) 0 8))))

(defun seed->keypair (seed)
  (let* ((seed (as-octets seed))
         (priv (ironclad:make-private-key :ed25519 :x seed)))
    (unless (= 32 (length seed)) (ton-error "ed25519 seed must be 32 bytes"))
    (%make-keypair seed (getf (ironclad:destructure-private-key priv) :y))))

(defun pbkdf2-sha512 (password salt iterations)
  (ironclad:derive-key (ironclad:make-kdf :pbkdf2 :digest :sha512)
                       (as-octets password) (as-octets salt) iterations 64))

(defun ascii (string) (sb-ext:string-to-octets string :external-format :utf-8))

(defun mnemonic->keypair (words &key (password ""))
  "TON mnemonic (24 words) -> KEYPAIR, as in tonlib / @ton/crypto:
entropy = HMAC-SHA512(words, password); seed = PBKDF2(entropy, \"TON default seed\", 100000)."
  (let* ((words (if (stringp words)
                    (remove "" (uiop:split-string (string-downcase (string-trim " " words))
                                                  :separator '(#\Space #\Newline #\Tab))
                            :test #'equal)
                    (mapcar #'string-downcase words)))
         (phrase (format nil "~{~A~^ ~}" words))
         (hmac (ironclad:make-hmac (ascii phrase) :sha512)))
    (unless (= 24 (length words))
      (ton-error "Expected a 24-word mnemonic, got ~D words" (length words)))
    (ironclad:update-hmac hmac (ascii password))
    (let ((entropy (ironclad:hmac-digest hmac)))
      (when (string= password "")
        ;; is_basic_seed(): PBKDF2(entropy, "TON seed version", 390)[0] == 0
        (unless (zerop (aref (pbkdf2-sha512 entropy (ascii "TON seed version") (max 1 (floor 100000 256))) 0))
          (ton-error "Mnemonic checksum failed (not a valid TON mnemonic)")))
      (seed->keypair (subseq (pbkdf2-sha512 entropy (ascii "TON default seed") 100000) 0 32)))))

(defun sign-octets (keypair octets)
  (ironclad:sign-message (ironclad:make-private-key :ed25519 :x (keypair-secret keypair))
                         (as-octets octets)))

(defun sign-cell (keypair cell)
  "Ed25519 signature (64 bytes) over the cell's representation hash."
  (sign-octets keypair (cell-hash cell)))

;;; --- Wallet V5R1 -------------------------------------------------------

;; https://github.com/ton-blockchain/wallet-contract-v5/blob/4fab977f4fae3a37c1aac216ed2b7e611a9bc2af/build/wallet_v5.compiled.json
(defparameter *wallet-v5r1-code-hex*
  "b5ee9c7241021401000281000114ff00f4a413f4bcf2c80b01020120020d020148030402dcd020d749c120915b8f6320d70b1f2082106578746ebd21821073696e74bdb0925f03e082106578746eba8eb48020d72101d074d721fa4030fa44f828fa443058bd915be0ed44d0810141d721f4058307f40e6fa1319130e18040d721707fdb3ce03120d749810280b99130e070e2100f020120050c020120060902016e07080019adce76a2684020eb90eb85ffc00019af1df6a2684010eb90eb858fc00201480a0b0017b325fb51341c75c875c2c7e00011b262fb513435c280200019be5f0f6a2684080a0eb90fa02c0102f20e011e20d70b1f82107369676ebaf2e08a7f0f01e68ef0eda2edfb218308d722028308d723208020d721d31fd31fd31fed44d0d200d31f20d31fd3ffd70a000af90140ccf9109a28945f0adb31e1f2c087df02b35007b0f2d0845125baf2e0855036baf2e086f823bbf2d0882292f800de01a47fc8ca00cb1f01cf16c9ed542092f80fde70db3cd81003f6eda2edfb02f404216e926c218e4c0221d73930709421c700b38e2d01d72820761e436c20d749c008f2e09320d74ac002f2e09320d71d06c712c2005230b0f2d089d74cd7393001a4e86c128407bbf2e093d74ac000f2e093ed55e2d20001c000915be0ebd72c08142091709601d72c081c12e25210b1e30f20d74a111213009601fa4001fa44f828fa443058baf2e091ed44d0810141d718f405049d7fc8ca0040048307f453f2e08b8e14038307f45bf2e08c22d70a00216e01b3b0f2d090e2c85003cf1612f400c9ed54007230d72c08248e2d21f2e092d200ed44d0d2005113baf2d08f54503091319c01810140d721d70a00f2e08ee2c8ca0058cf16c9ed5493f2c08de20010935bdb31e1d74cd0b4d6c35e")

(defvar *wallet-v5r1-code* nil)

(defun wallet-v5r1-code ()
  (or *wallet-v5r1-code*
      (setf *wallet-v5r1-code* (first (parse-boc (hex->octets *wallet-v5r1-code-hex*))))))

(defconstant +mainnet-global-id+ -239)
(defconstant +testnet-global-id+ -3)
(defconstant +op-v5-signed-external+ #x7369676e)
(defconstant +op-action-send-msg+ #x0ec3c86d)

(defun wallet-v5r1-id (&key (network-global-id +mainnet-global-id+) (workchain 0) (subwallet 0))
  "wallet_id = network_global_id XOR context, context = 1:1 wc:int8 version:uint8(0) subwallet:uint15,
as a signed 32-bit integer."
  (let* ((ctx-cell (build-cell (store-uint 1 1) (store-int workchain 8) (store-uint 0 8)
                               (store-uint subwallet 15)))
         (ctx (load-int (cell-slice ctx-cell) 32))
         (id (logxor network-global-id ctx)))
    (if (logbitp 31 (ldb (byte 32 0) id))
        (- (ldb (byte 32 0) id) (ash 1 32))
        (ldb (byte 32 0) id))))

(defstruct (wallet-v5r1 (:constructor %make-wallet-v5r1) (:copier nil))
  (keypair nil :read-only t)
  (wallet-id 0 :type integer :read-only t)
  (workchain 0 :read-only t)
  (state-init nil :read-only t)
  (address nil :read-only t))

(defun make-wallet-v5r1 (keypair &key (workchain 0) (network-global-id +mainnet-global-id+) (subwallet 0))
  (let* ((wallet-id (wallet-v5r1-id :network-global-id network-global-id
                                    :workchain workchain :subwallet subwallet))
         (data (build-cell (store-bit 1)                 ; is_signature_allowed
                           (store-uint 0 32)             ; seqno
                           (store-int wallet-id 32)
                           (store-bytes (keypair-public keypair))
                           (store-bit 0)))               ; extensions dict = empty
         (state-init (make-state-init (wallet-v5r1-code) data)))
    (%make-wallet-v5r1 :keypair keypair :wallet-id wallet-id :workchain workchain
                       :state-init state-init
                       :address (state-init-address state-init :workchain workchain))))

(defun wallet-address (w) (wallet-v5r1-address w))
(defun wallet-state-init (w) (wallet-v5r1-state-init w))

(defun wallet-seqno (getter wallet)
  "seqno getter; 0 for a not-yet-deployed wallet (signalled by the getter)."
  (handler-case (first (funcall getter (wallet-address wallet) "seqno" '()))
    (error () 0)))

(defconstant +send-mode-pay-gas-separately+ 1)
(defconstant +send-mode-ignore-errors+ 2)

(defun out-list-cell (relaxed-messages &key (mode (logior +send-mode-pay-gas-separately+
                                                          +send-mode-ignore-errors+)))
  "OutList: out_list$_ prev:^(OutList n) action:OutAction, built from the
empty list outwards.  V5 external requests must carry mode +2."
  (reduce (lambda (prev msg)
            (build-cell (store-ref prev)
                        (store-uint +op-action-send-msg+ 32)
                        (store-uint mode 8)
                        (store-ref msg)))
          relaxed-messages
          :initial-value (end-cell (begin-cell))))

(defun wallet-external-message (wallet &key messages seqno (valid-until (+ (unix-now) 60))
                                            (deploy nil))
  "Signed external message for WALLET carrying MESSAGES (MESSAGE-SPEC list):
   signed_external#7369676e wallet_id:int32 valid_until:uint32 seqno:uint32
   actions:(Maybe ^OutList) has_other_actions:(## 1) signature:bits512
Returns (values EXTERNAL-MESSAGE-CELL BODY-CELL)."
  (when (> (length messages) 255) (ton-error "Too many messages"))
  (let* ((relaxed (mapcar #'message-spec->relaxed messages))
         (unsigned (let* ((b (store-uint (begin-cell) +op-v5-signed-external+ 32))
                          (b (store-int b (wallet-v5r1-wallet-id wallet) 32))
                          (b (store-uint b valid-until 32))
                          (b (store-uint b seqno 32))
                          (b (store-maybe-ref b (and relaxed (out-list-cell relaxed))))
                          (b (store-bit b 0)))
                     b))
         (signature (sign-cell (wallet-v5r1-keypair wallet) (end-cell unsigned)))
         (body (end-cell (store-bytes unsigned signature))))
    (values (external-message :to (wallet-address wallet) :body body
                              :state-init (and deploy (wallet-state-init wallet)))
            body)))

(defun external-message-normalized-hash (to body)
  "Hash of the NORMALIZED external-in message for a body sent to TO: src
addr_none, import_fee 0, no StateInit, body always by reference.  This is
the form explorers and indexers key an external message by, and does not
change whether the wallet was deployed in the same message or how the body
happened to be inlined, so it is one of the identities a broadcast is
matched on (see TRANSACTION-MATCHES-BROADCAST-P in tonlib.lisp)."
  (cell-hash (end-cell (let* ((b (begin-cell))
                              (b (store-uint b #b10 2))   ; ext_in_msg_info$10
                              (b (store-address b nil))   ; src
                              (b (store-address b to))    ; dest
                              (b (store-coins b 0))       ; import_fee
                              (b (store-bit b 0))         ; init: nothing
                              (b (store-bit b 1)))        ; body: ^X
                         (store-ref b body)))))

(defun wallet-from-mnemonic-source (&optional key)
  "Mnemonic from TON_MNEMONIC or the file named by TON_MNEMONIC_FILE, or,
when KEY is given (a symbol or string, e.g. :MOMENTUM), from
TON_<KEY>_MNEMONIC / TON_<KEY>_MNEMONIC_FILE instead -- so a bot running
several strategies can fund them from different wallets by setting
different env vars per strategy, while a single TON_MNEMONIC still covers
everything that doesn't ask for its own KEY.  The words are never printed."
  (let* ((prefix (if key (format nil "TON_~:@(~A~)_" key) "TON_"))
         (env (uiop:getenv (format nil "~AMNEMONIC" prefix)))
         (file (uiop:getenv (format nil "~AMNEMONIC_FILE" prefix))))
    (cond ((and env (plusp (length env))) (make-wallet-v5r1 (mnemonic->keypair env)))
          ((and file (plusp (length file)))
           (unless (probe-file file)
             (ton-error "~AMNEMONIC_FILE ~A does not exist" prefix file))
           (make-wallet-v5r1 (mnemonic->keypair (uiop:read-file-string file))))
          (t nil))))

(defvar *wallet* nil "Wallet loaded with WALLET-FROM-MNEMONIC")

(defun wallet-from-mnemonic (&optional mnemonic)
  "Load the V5R1 wallet into the image from MNEMONIC (a string of 24 words)
Only the address is returned; the words are never echoed or logged."
  (setf *wallet* (if mnemonic
                     (make-wallet-v5r1 (mnemonic->keypair mnemonic))
                     (ton-error "no mnemonic given"))))
