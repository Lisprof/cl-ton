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
   :call-with-getter-retry :definitive-getter-failure-p :*getter-retry-attempts* :*getter-retry-delay*
   ;; boc (formerly the separate :ton-boc package; see src/ton-boc.lisp)
   :boc-error
   :builder :builder-p :begin-cell :build-cell
   :builder-bits :builder-bit-length :builder-refs :builder-exotic-p
   :store-bit :store-bits :store-uint :store-int :store-bytes
   :store-bit-vector :store-ref :store-builder :end-cell
   :node :node-p :node-hash :node-hash-hex :node-depth :node-level :node-equal
   :node-level-mask :node-hashes :node-depths :node-hash-at :node-depth-at
   :cell-special-type :pruned-branch-p :make-pruned-branch
   :merkle-proof-root :verify-merkle-proof :verify-merkle-update :merkle-update-hashes
   ;; proof-verify.lisp
   :proof-error :dict-lookup :parse-block-info :verify-block-proof :parse-shard-state-header
   :find-shard-description :verify-account-state :verify-transaction-list :parse-transaction-header
   :parse-account :run-account-get-method :open-lite-client :close-lite-client :lite-call :lite-sync :lite-account-state :lite-transactions :lite-run-get-method :lite-server-get-method :lite-send-message :lite-shards :lite-shard-info :lite-libraries :lite-lookup-block :lite-prove-block :diagnose-lite :*signature-set-counts* :lite-error :lite-error-code :lite-client-trusted
   :verify-all-shards-info :list-shard-descriptions :verify-libraries-with-proof :verify-shard-info :lookup-shard-leaf :verify-lookup-block :verify-shard-block-proof :verify-lookup-header :verify-lookup-prev-header :parse-block-links :verify-libraries :check-send-message-status :external-message-hash :verify-block-header :verify-block-data :verify-block-transactions :find-block-transaction :dict-lookup-in-slice
   ;; sync.lisp
   :validator-set :validator-set-p :validator-set-since :validator-set-until :validator-set-main
   :validator-set-total-weight :validator-set-members :parse-validator-set :validator-set-active-p
   :check-block-signatures :plan-block-signatures :check-signature-entries :check-signature-jobs :ed25519-prepare :ed25519-batch-verify :ed25519-first-invalid :ironclad-assembly-status :ironclad-assembly-line :*lite-proof-hook* :save-link-vector :load-link-vector :parallel-map :worker-count :*worker-count* :ed25519-key-point :masterchain-config-root :key-block-config-root :config-param :validator-sets-at :validator-sets-at-root :key-block-validator-sets
   :verify-forward-link :signature-message :verify-back-link :verify-partial-block-proof :proof-single-links :parse-catchain-config :verify-config-info
   :compute-validator-set-hash :shuffle-masterchain-validators :masterchain-validator-set-hash
   :check-validator-set-binding :*verify-validator-set-hash* :prng-next-ulong :make-validator-prng
   :cell :cell-p :make-cell
   :cell-bits :cell-bit-length :cell-refs :cell-exotic-p
   :cell-bit :cell-uint :cell-bit-vector :cell-data-octets
   :cell-hash :cell-hash-hex :cell-depth :cell-level 
   :absent-cell :absent-cell-p :make-absent-cell
   :collect-nodes :parse-boc :crc32c
   :pmap :*worker-count* :*parallel-threshold*
   :octets :octets->hex :hex->octets
   :as-octets :uint->octets :octets->uint :concat-octets :sha256
   :run-boc-tests
   ;; conditions  
   :ton-error :tonlib-error :tonlib-error-code :tonlib-error-message :emulator-error  
   ;; tl.lisp: TL serialization primitives
   :tl-error :crc32-ieee :tl-constructor-id :make-tl-buffer :tl-buffer-octets
   :tl-write-uint :tl-write-int32 :tl-write-int64 :tl-write-int256 :tl-write-raw
   :tl-write-bytes :tl-write-string :tl-write-vector
   :make-tl-reader :tl-reader-remaining :tl-reader-eof-p :tl-take :tl-read-uint
   :tl-read-int32 :tl-read-int64 :tl-read-int256 :tl-read-bytes :tl-read-string :tl-read-vector
   ;; tl.lisp: the typed tonlib API (cl-ton/tests/tl/tonlib_api.tl)
   :tlapi-make :tlapi-validate :tlapi-get :tlapi-is :tlapi-obj :tlapi-obj-p :tlapi-obj-name
   :tlapi-function-p :tlapi-constructor-names :tlapi->plist :json->tlapi
   ;; adnl-crypto.lisp
   :x25519 :x25519-reference :adnl-shared-secret :adnl-key-id :ed25519-public-from-seed :ed25519-pub->x25519-pub
   :ed25519-clamped-scalar-octets :make-aes-ctr :aes-ctr-process :adnl-handshake-key-iv
   :sha512-octets :octets-le->int :int->octets-le
   ;; adnl.lisp
   :adnl-error :adnl-session :adnl-session-p :adnl-client-handshake-packet :adnl-server-accept-handshake
   :adnl-encode-packet :adnl-decode-packet :adnl-parse-message :adnl-connect :adnl-close :adnl-send
   :adnl-receive :adnl-query :adnl-ping :adnl-serve :adnl-stop-server :random-octets
   :tl-encode-tcp-ping :tl-encode-tcp-pong :tl-encode-adnl-query :tl-encode-adnl-answer :tl-encode-lite-query
   ;; proxy-liteserver-native.lisp
   :open-native-proxy-liteserver :close-native-proxy-liteserver :native-proxy :native-proxy-p :native-proxy-port
   :native-proxy-pub :native-proxy-db :native-proxy-ready-upstreams :write-native-proxy-identity
   :read-native-proxy-identity :native-proxy-config-json :describe-lite-query :encode-lite-server-error
   :global-config-liteservers :ip-int->dotted :ed25519-sign
   ;; base64  
   :base64-encode :base64-decode :cell->base64 :base64->cell  
   ;; slice  
   :slice :slice-p :cell-slice :slice-remaining-bits :slice-remaining-refs  
   :load-uint :load-int :load-bit :load-coins :load-address :load-ref  
   :load-maybe-ref :load-bytes :skip-bits :slice-empty-p :slice-rest-bits  
   ;; types  
   :address :address-p :make-address :address-workchain :address-hash  
   :parse-address :address->string :address->raw-string :address-equal  
   :store-address :store-coins :store-maybe-ref :store-either-ref  
   :nano :from-nano :usdt-units :from-usdt-units  
   :make-state-init :state-init-address  
   :internal-message-relaxed :external-message :serialize-boc  
   ;; vm-stack  
   :stack-slice :stack-null  
   :serialize-vm-stack :parse-vm-stack  
   ;; tonlib  
   :tonlib :tonlib-oracle :tonlib-json-op :*tonlib-oracle* :open-tonlib :close-tonlib :with-tonlib :tonlib-call :ensure-keystore
   :tonlib-masterchain-info :tonlib-masterchain-block :tonlib-shards
   :transient-error-p :stack-item-key :make-raw-message :make-raw-transaction :raw-tx-utime :raw-tx-data :raw-tx-lt :raw-tx-hash :raw-tx-fee :raw-tx-storage-fee
   :raw-tx-other-fee :raw-tx-in-msg :raw-tx-out-msgs :raw-msg-hash :raw-msg-body-hash :raw-msg-source :raw-msg-destination
   :raw-msg-value :raw-msg-fwd-fee :raw-msg-ihr-fee :raw-msg-created-lt :raw-msg-body :raw-msg-init-state
   :make-short-tx-id :short-tx-account :short-tx-lt :short-tx-hash :make-block-id :block-id-workchain :block-id-shard :block-id-seqno :block-id-root-hash :block-id-file-hash  
   :tonlib-block-transactions :tonlib-sync :tonlib-account-state :account-state  
   :account-state-balance :account-state-code :account-state-data  
   :account-state-last-lt :account-state-last-hash :account-state-status  
   :tonlib-run-get-method :make-tonlib-getter :make-local-getter :tonlib-send-message :*get-method-block*
   :tonlib-config-cell :tonlib-shard-account-cell :tonlib-libraries :collect-library-hashes :library-cell-hash :tonlib-transactions
   :transaction-out-count
   :transaction-matches-broadcast-p
   ;; emulator  
   :load-emulator-library :run-get-method-local :emulate-external-message :emulate-message :parse-message-header :funded-shard-account :emulation-result  
   :load-tonlib-library  
   ;; proxy-liteserver
   :proxy-liteserver :proxy-liteserver-p :proxy-liteserver-port :proxy-liteserver-process
   :proxy-liteserver-binary :proxy-liteserver-db :proxy-liteserver-global-config
   :validate-proxy-liteserver-preconditions
   :open-proxy-liteserver :*proxy-liteserver-implementation* :close-proxy-liteserver :proxy-liteserver-alive-p :open-tonlib-via-proxy :check-routed-config
   :read-proxy-liteserver-identity :proxy-liteserver-entry :proxy-liteserver-config
   :proxy-liteserver-global-config-path :ipv4-string->ip-int
   ;; proxy diagnostics (where does the native proxy stop?)
   :proxy-refresh-liteservers :proxy-merge-liteservers :*proxy-refresh-url* :*proxy-fetch-function* :*proxy-official-config-urls*
   :proxy-save-scores :proxy-scores-file :proxy-diagnostics :proxy-diagnostics-report :proxy-verdict :proxy-wait-ready :start-proxy-watch
   :diagnose-proxy :adnl-ext-client-status :adnl-failure-hint
   :adnl-ext-server-connection-stats :proxy-method-table :proxy-history-query-p :*proxy-max-attempts* :*proxy-hedge-delay* :*proxy-hedge-min* :*proxy-hedge-max*
   :*proxy-failure-penalty-max* :proxy-hedge-delay :*proxy-max-active-upstreams*
   :proxy-activate-standby :start-adnl-ext-client
   :*tonlib-sync-retry-delay* :proxy-ok-count :proxy-progress-function :proxy-network-summary :derived-keystore
   :*proxy-failure-penalty* :*proxy-history-queries*
   :emulation-result-success-p :emulation-result-error :emulation-result-exit-code  
   :emulation-result-fees :emulation-result-vm-log :emulation-result-out-messages  
   :emulator-version :method-id :unix-now
   :load-hm-label :dict-entries :transaction-messages :parse-message-summary
   :emulation-out-message-cells :emulation-out-messages-summary :emulation-result-shard-account
   :external-message-normalized-hash
   ;; jetton  
   :jetton-transfer-body :jetton-wallet-address :jetton-wallet-balance :address-slice
   ;; dex: the bare DEX-agnostic protocol shape only (see dex.lisp) -- no
   ;; methods, no addresses, no contract knowledge. Every DEFMETHOD/DEFUN
   ;; dispatch and every pool/router/factory/master address lives in the
   ;; trader (src/dex-config.lisp and its per-DEX modules dex-stonfi.lisp/
   ;; dex-dedust.lisp/dex-storm.lisp).
   :message-spec :message-spec-to :message-spec-value :message-spec-body :message-spec-state-init :make-message-spec
   :dex-resolve :dex-id :dex-pool-address :dex-pool-state
   :dex-swap-ton->usdt :dex-swap-cycle
   ;; wallet  
   :keypair :keypair-public :mnemonic->keypair :seed->keypair  
   :wallet-v5r1 :make-wallet-v5r1 :wallet-v5r1-p :wallet-address :wallet-state-init  
   :wallet-seqno :wallet-external-message :sign-cell :wallet-v5r1-id  
   :wallet-v5r1-code :wallet-from-mnemonic-source :wallet-from-mnemonic :*wallet*
   ;; indexer  
   :flow-event :flow-event-pool :flow-event-block :flow-event-transaction
   :flow-event-observed-at :*flow-event-hook* :flow-scanner :start-flow-scanner :stop-flow-scanner  
   :drain-flow-events :*flow-event-backlog* :publish-flow-event :scan-confirmed-flow-once  
   ;; chain protocol  
   :chain :chain-pools :chain-ton-balance :chain-usdt-balance :chain-wallet-deployed-p
   :chain-jetton-balance :chain-wallet-transactions :chain-drain-flow-events
   :chain-wallet-seqno :chain-send :chain-emulate :chain-now :chain-sleep :chain-wait-block  
   :chain-set-wallet :chain-getter :chain-close :tonlib-chain :make-tonlib-chain :wait-until
   :head-poller :start-head-poller :stop-head-poller))
