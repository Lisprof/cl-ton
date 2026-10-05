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

;;;; jetton.lisp -- TEP-74 jetton helpers.

(in-package :cl-ton)

(defconstant +op-jetton-transfer+ #x0f8a7ea5)
(defconstant +op-jetton-transfer-notification+ #x7362d09c)
(defconstant +op-jetton-internal-transfer+ #x178d4519)
(defconstant +op-excesses+ #xd53276db)

(defun jetton-transfer-body (&key (query-id 0) amount destination response-destination
                                  custom-payload (forward-ton-amount 0) forward-payload)
  "transfer#0f8a7ea5 query_id:uint64 amount:(VarUInteger 16) destination:MsgAddress
   response_destination:MsgAddress custom_payload:(Maybe ^Cell)
   forward_ton_amount:(VarUInteger 16) forward_payload:(Either Cell ^Cell)"
  (let* ((b (store-uint (begin-cell) +op-jetton-transfer+ 32))
         (b (store-uint b query-id 64))
         (b (store-coins b amount))
         (b (store-address b destination))
         (b (store-address b response-destination))
         (b (store-maybe-ref b custom-payload))
         (b (store-coins b forward-ton-amount))
         (b (if forward-payload (store-either-ref b forward-payload) (store-bit b 0))))
    (end-cell b)))

(defun address-slice (addr)
  "A slice holding just a MsgAddress, the form getters expect."
  (cell-slice (end-cell (store-address (begin-cell) addr))))

(defun jetton-wallet-address (getter master owner)
  "get_wallet_address(owner) on the jetton MASTER via GETTER, a function
(address method stack) -> items."
  (let ((items (funcall getter master "get_wallet_address" (list (address-slice owner)))))
    (or (load-address (first items))
        (ton-error "get_wallet_address returned addr_none"))))

(defun jetton-wallet-balance (getter wallet)
  "get_wallet_data -> balance (first stack item).  Uninitialised wallets
signal; callers treat that as a zero balance."
  (first (funcall getter wallet "get_wallet_data" '())))
