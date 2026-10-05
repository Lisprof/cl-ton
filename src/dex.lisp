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

;;;; dex.lisp -- the DEX-agnostic protocol shape, declared and nothing
;;;; more.
;;;;
;;;; No methods, no addresses, no contract knowledge.
;;;; cl-ton itself never resolves a pool, quotes a swap, or knows a single
;;;; contract address; it only names the shape a caller can rely on.

(in-package :cl-ton)

(defgeneric dex-resolve (getter config)
  (:documentation "Resolves CONFIG (a DEX-specific config struct) against
live/emulated chain state via GETTER into that DEX's own resolved-identity
struct."))

(defgeneric dex-id (dex)
  (:documentation "A keyword identifying which DEX/version DEX is (e.g.
:STONFI-V1, :STONFI-V2, :DEDUST, :STORM)."))

(defgeneric dex-pool-address (dex)
  (:documentation "DEX's own pool/market address."))

(defgeneric dex-pool-state (getter dex)
  (:documentation "DEX's current pool state (reserves, fees, ...) via GETTER."))

(defgeneric dex-swap-ton->usdt (dex &rest keys &key user amount min-out deadline query-id)
  (:documentation "A MESSAGE-SPEC swapping native TON for USDT on DEX."))

(defgeneric dex-swap-usdt->ton (dex &rest keys &key user user-usdt-wallet amount min-out deadline query-id)
  (:documentation "A MESSAGE-SPEC swapping USDT for native TON on DEX."))

(defgeneric dex-swap-cycle (dex &rest keys)
  (:documentation "A single MESSAGE-SPEC executing a whole multi-hop cycle
atomically on DEX, when DEX supports one; signals an error otherwise."))
