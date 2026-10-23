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

;;; cl-ton.asd

(asdf:defsystem "cl-ton"  
  :description "Reusable Common Lisp TON client: BOC, tonlib, emulator, DEX, wallet, chain, indexer"  
  :depends-on ("ironclad" "cffi" "jonathan"
               (:require "sb-bsd-sockets") (:require "sb-concurrency"))  
  :serial t  
  :components  
  ((:module "src"  
    :serial t  
    :components
    ((:file "package")
     (:file "json")          ; the one place that touches JSON (libemulator results, config files)
     (:file "ton-boc")
     (:file "errors")  
     (:file "base64")  
     (:file "slice")  
     (:file "tl")            ; the TL codec (no schema data in it)
			     (:file "tl-schema")     ; GENERATED: the lite_api / ton_api / tonlib_api schemas as Lisp data
     (:file "types")  
     (:file "vm-stack")  
     (:file "tonlib")  
     (:file "emulator")
     (:file "ed25519-batch") ; many Ed25519 signatures at once, pure, on ironclad's curve operations
     (:file "proof-verify") ; checking a liteserver answer against a trusted block hash
     (:file "sync")         ; trusted block -> newer block: validator signatures over block links  
     (:file "jetton")  
     (:file "wallet")  
     (:file "adnl-ext")            ; Phase B: X25519 glue, AES-CTR framing, init packet
     (:file "adnl-ext-client")     ; Phase C: outbound upstream client (reconnect loop, query table)
     (:file "adnl-ext-server")     ; Phase D: inbound listener/handshake, shared with fakechain
     (:file "proxy-liteserver")    ; uses CONFIG-WITH-LITESERVERS/JSON-GET from tonlib
     (:file "lite-client")         ; verifying liteserver client: sync, account state, transactions, getters
     (:file "lite-backend")        ; the lite client as a drop-in for the tonlib client (R2b)
     (:file "dex")  
     (:file "indexer")     ; before chain: chain-close calls stop-flow-scanner  
     (:file "chain"))))  
  :in-order-to ((test-op (test-op "cl-ton/test"))))  
  
(asdf:defsystem "cl-ton/test"  
  :description "Network-free tests for the reusable cl-ton (BOC + SDK vectors)"  
  :depends-on ("cl-ton")  
  :serial t  
  :components ((:module "tests"  
                :serial t  
                :components (
			     (:file "files")         ; BUNDLED-ENV-BINARY: locates the fift/proxy-liteserver released
                                             ; binaries (test environment only): <bin>/env/ or beside the
                                             ; binary, cl-ton/tests/ in a checkout, TON_*_BINARY, PATH
			     (:file "tl-generate")   ; the generator of src/tl-schema.lisp from the vendored .tl files (test-side)
			     (:file "tonlib-oracle") ; the JSON tonlib (libtonlibjson via CFFI): a TEST ORACLE, not part of the lean build
			     (:file "fakechain")     ; the emulator-backed liteserver (the test network), tests only
			     (:file "client")
			     (:file "fake-chain")
			     (:file "tl-adnl-ext")
			     (:file "proxy-ext")
			     (:file "scenarios")
			     (:file "tlapi")
			     (:file "cells")
			     (:file "verify")
			     (:file "sync")
			     (:file "lite")
			     (:file "coverage"))))   ; Stage 3: code the other suites never ran   ; validator sets, signatures, block links   ; the lite proof verifier   ; cell levels, pruned branches, Merkle proofs   ; the typed tonlib API: schema, validation, JSON bridge, A/B vs tonlibjson

  :perform (test-op (o c)  
             (uiop:symbol-call :cl-ton/test :run-tests)))  
