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

;;;; client-package.lisp -- the reusable TON client package.  
  
(defpackage :cl-ton
  (:nicknames :ton-client)
  (:use :cl)
  ;; the few jonathan functions the application uses, all of them in json.lisp
  (:import-from :jonathan :parse :to-json :*false-value* :*null-value*)
   (:export
   ;; tonlib.lisp: resolve-time getter retry
 :call-with-getter-retry :definitive-getter-failure-p
   ;; boc (formerly the separate :ton-boc package; see src/ton-boc.lisp)
 :builder :begin-cell
 :store-bit :store-uint :store-int :store-bytes
 :store-ref :end-cell
   ;; proof-verify.lisp
 :diagnose-lite
   ;; sync.lisp
 :cell
 :cell-hash
 :pmap
   ;; conditions  
 :ton-error
   ;; tl.lisp: TL serialization primitives
   ;; tl.lisp: the typed tonlib API (cl-ton/tests/tl/tonlib_api.tl)
 :tlapi-make :tlapi-get :tlapi-is
   ;; adnl-crypto.lisp
   ;; adnl.lisp
   ;; proxy-liteserver-native.lisp
   ;; base64  
   ;; slice  
 :cell-slice
 :load-uint :load-int :load-address
 :load-bytes
   ;; types  
 :address :address-p :make-address :address-workchain :address-hash
 :parse-address :address->string :address-equal
 :store-address :store-coins :store-maybe-ref :store-either-ref
 :nano :from-nano :usdt-units :from-usdt-units
 :external-message :serialize-boc
   ;; vm-stack  
 :stack-slice
   ;; tonlib  
 :tonlib :tonlib-oracle :open-tonlib :close-tonlib :ensure-keystore
 :tonlib-masterchain-info
 :lite-execute :lite-execute-supported :proof-trusted-block :verify-proof
 :proof->octets :octets->proof :transient-error-p :stack-item-key
 :block-id-seqno
 :make-tonlib-getter :*get-method-block*
 :transaction-out-count
 :transaction-matches-broadcast-p
   ;; emulator  
 :load-emulator-library
   ;; proxy-liteserver
 :proxy-liteserver :proxy-liteserver-port
 :proxy-liteserver-binary :proxy-liteserver-db
 :open-proxy-liteserver :*proxy-liteserver-implementation* :close-proxy-liteserver :check-routed-config
 :proxy-liteserver-global-config-path
   ;; proxy diagnostics (where does the native proxy stop?)
 :start-proxy-watch
 :diagnose-proxy
 :derived-keystore
 :emulation-result-success-p :emulation-result-error :emulation-result-exit-code
 :emulation-result-fees :emulation-result-out-messages
 :unix-now
 :external-message-normalized-hash
   ;; jetton  
 :jetton-transfer-body :jetton-wallet-address :address-slice
   ;; dex: the bare DEX-agnostic protocol shape only (see dex.lisp) -- no
   ;; methods, no addresses, no contract knowledge. Every DEFMETHOD/DEFUN
   ;; dispatch and every pool/router/factory/master address lives in the
   ;; trader (src/dex-config.lisp and its per-DEX modules dex-stonfi.lisp/
   ;; dex-dedust.lisp/dex-storm.lisp).
 :message-spec :message-spec-to :message-spec-value :make-message-spec
   ;; wallet  
 :mnemonic->keypair
 :wallet-v5r1 :make-wallet-v5r1 :wallet-address
 :wallet-external-message
 :wallet-from-mnemonic-source :wallet-from-mnemonic :*wallet*
   ;; indexer  
 :flow-event-pool
 :*flow-event-hook* :start-flow-scanner :stop-flow-scanner
   ;; chain protocol  
 :chain :chain-pools :chain-ton-balance :chain-usdt-balance :chain-wallet-deployed-p
 :chain-jetton-balance :chain-wallet-transactions :chain-drain-flow-events
 :chain-wallet-seqno :chain-send :chain-emulate :chain-now :chain-wait-block
 :chain-set-wallet :chain-getter :chain-close :tonlib-chain :make-tonlib-chain :wait-until
 :head-poller :start-head-poller :stop-head-poller))
