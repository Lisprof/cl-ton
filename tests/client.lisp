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

;;;; tests/client.lisp -- network-free tests for the reusable cl-ton.  
;;;; Cross-checks BOC/address/slice/wallet/DEX math against tests/vectors.json.  

(eval-when (:compile-toplevel :load-toplevel :execute)
  (require :sb-posix))  ; TON_MNEMONIC / TON_MNEMONIC_FILE env-var tests

(defpackage :cl-ton/test  
  (:use
   :cl :cl-ton)  
  (:shadow
   #:run-tests)
  (:export
   :*failures* :*checks* :check :skip-missing :strict-tests-p :fake-address
   :*test-keypair* #:run-tests :find-proxy-liteserver-binary
   :fake-chain :make-fake-chain :fake-pools :fake-ton :fake-usdt
   :fake-seqno :fake-now :fake-head :fake-block-waits :fake-script
   :fake-pending :fake-sent :fake-emulate-fn :fake-pool-hook
   :fake-jettons :fake-jetton-balance :fake-txs :fake-flow-events :fake-wallet-txs-fn
   :make-fake-tx
   ;; generic vector/cell-comparison test helpers, reused by the trader's
   ;; own DEX vector tests (tests/dex-unit.lisp) -- the DEX-specific tests
   ;; themselves (STON.fi/DeDust/Storm, TEST-POOLS/TEST-DEXES) moved there
   ;; with the DEX code (see ton-trader.asd's relocation note): CL-TON's
   ;; own tests now cover only blockchain-generic primitives.
   :vectors :v :same-cell-p :cell-of-hex :check-message-spec :*user*))
  
(in-package :cl-ton/test)  
  
(defvar *failures* 0)  
(defvar *checks* 0)
  
(defmacro check (name form)  
  `(progn  
     (incf *checks*)  
     (handler-case  
         (if ,form  
             (format t "  ok   ~A~%" ,name)  
             (progn (incf *failures*) (format t "  FAIL ~A~%" ,name)))  
       (error (e) (incf *failures*) (format t "  FAIL ~A: ~A~%" ,name e)))))  
  
;;; --- skip policy (one rule for the whole project) ---------------------------
;;; A test that needs an optional native piece (tonlib/libemulator .so, the released
;;; proxy-liteserver, fift) calls SKIP-MISSING when it is absent: it prints
;;; "  skip <what>" and counts as neither pass nor fail.  With TON_TEST_STRICT=1 (CI
;;; with the full toolchain) the same call is a FAILED check instead, so a build
;;; that silently lost a native dependency cannot go green.
(defvar *strict-override* :unset
  "Bind to T/NIL to override TON_TEST_STRICT (used by the policy's own test).")

(defun strict-tests-p ()
  (if (eq *strict-override* :unset)
      (equal (uiop:getenv "TON_TEST_STRICT") "1")
      *strict-override*))

(defun skip-missing (what)
  (if (strict-tests-p)
      (check (format nil "~A is available (TON_TEST_STRICT=1 forbids skipping)" what) nil)
      (format t "  skip ~A~%" what)))

(defun test-skip-policy ()
  (format t "skip policy~%")
  (let ((out (with-output-to-string (*standard-output*)
               (let ((*strict-override* nil)) (skip-missing "x")))))
    (check "non-strict: a missing dependency prints a skip line" (search "skip x" out)))
  (let ((c *checks*) (f *failures*))
    (let ((*strict-override* t))
      (with-output-to-string (*standard-output*) (skip-missing "x")))
    (let ((failed (- *failures* f)))
      ;; undo the deliberately provoked failure so the run stays honest
      (setf *failures* f *checks* c)
      (check "strict: a missing dependency is a failed check, not a skip" (= failed 1)))))

(defparameter *vectors*
  (jonathan:parse
   (uiop:read-file-string (asdf:system-relative-pathname "cl-ton" "../tests/vectors.json"))
   :as :hash-table)
  "Read and parsed once, when this file is loaded -- not on every call to
VECTORS below.  This matters beyond just avoiding repeat file I/O: a
deployed `deploy`-built binary clears ASDF's source-tree bookkeeping at
build time (so it never tries to find or recompile source at runtime),
which means ASDF:SYSTEM-RELATIVE-PATHNAME can no longer resolve \"cl-ton\"
by the time such a binary actually runs -- but by then this DEFPARAMETER's
value was already computed at load time (during the build, before that
happens) and captured into the image by SAVE-LISP-AND-DIE, same as any
other in-memory value.  VECTORS doing its own fresh read on every call
would fail in exactly that deployed-with-tests scenario.")

(defun vectors () *vectors*)  
  
(defun v (obj &rest keys)  
  (apply #'cl-ton::json-get obj keys))  

(defun boc-hex (cell) (octets->hex (serialize-boc cell :has-crc32c t)))
(defun cell-of-hex (hex) (first (parse-boc (hex->octets hex))))
(defun same-cell-p (cell hex) (node-equal cell (cell-of-hex hex)))

(defparameter *user* (parse-address "EQBGhqLAZseEqRXz4ByFPTGV7SVMlI4hrbs-Sps_Xzx01x8G"))

(defun test-address (vec)
  (format t "address~%")
  (let ((a (v vec "address")))
    (check "parse/format friendly" (string= (address->string *user*) (v a "friendly")))
    (check "raw string" (string= (address->raw-string *user*) (v a "raw")))
    (check "non-bounceable" (string= (address->string *user* :bounceable nil) (v a "nonBounceable")))
    (check "parse raw" (address-equal (parse-address (v a "raw")) *user*))
    (check "parse non-bounceable" (address-equal (parse-address (v a "nonBounceable")) *user*))
    (check "bad checksum rejected"
           (handler-case (progn (parse-address "EQBGhqLAZseEqRXz4ByFPTGV7SVMlI4hrbs-Sps_Xzx01x8H") nil)
             (ton-error () t)))
    (check "store-address addr_std" (same-cell-p (end-cell (store-address (begin-cell) *user*)) (v a "cell")))
    (check "store-address addr_none" (same-cell-p (end-cell (store-address (begin-cell) nil)) (v a "none")))
    (check "load-address round trip"
           (address-equal (load-address (cell-slice (end-cell (store-address (begin-cell) *user*)))) *user*))
    (check "load-address none" (null (load-address (cell-slice (cell-of-hex (v a "none"))))))))

(defun test-coins (vec)
  (format t "coins~%")
  (dolist (entry (v vec "coins"))
    (let ((value (parse-integer (v entry "value"))))
      (check (format nil "store-coins ~D" value)
             (same-cell-p (end-cell (store-coins (begin-cell) value)) (v entry "cell")))
      (check (format nil "load-coins ~D" value)
             (= value (load-coins (cell-slice (cell-of-hex (v entry "cell"))))))))
  (check "internal message relaxed envelope"
         (same-cell-p (internal-message-relaxed :to *user* :value (nano 3/2)
                                                :body (end-cell (store-uint (begin-cell) #x12345678 32)))
                      (v vec "internalRelaxed"))))

(defun test-dict (vec)
  (format t "hashmap~%")
  (let* ((d (v vec "dict"))
         (entries (loop for key in (v d "keys") for i from 1
                        collect (cons (parse-integer key :radix 16)
                                      (let ((i i)) (lambda (b) (store-ref b (end-cell (store-uint (begin-cell) i 8)))))))))
    (check "Hashmap 256 ^Cell matches @ton/core"
           (same-cell-p (cl-ton::hashmap-cell entries 256) (v d "cell")))
    (check "empty HashmapE is a single 0 bit"
           (let ((c (end-cell (cl-ton::store-dict (begin-cell) '() 256))))
             (and (= 1 (cell-bit-length c)) (= 0 (cell-bit c 0)))))))

(defun test-jetton (vec)
  (format t "jetton~%")
  (let ((router (parse-address "EQCS4UEa5UaJLzOyyKieqQOQ2P9M-7kXpkO5HnP3Bv250cN3")))
    (check "TEP-74 transfer body"
           (same-cell-p (jetton-transfer-body :query-id 42 :amount 1000000 :destination router
                                              :response-destination *user*
                                              :forward-ton-amount (nano 24/100)
                                              :forward-payload (end-cell (store-uint (begin-cell) #xdeadbeef 32)))
                        (v vec "jettonTransfer")))))

(defun fake-address (byte)
  (make-address :workchain 0 :hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element byte)))

(defvar *test-keypair* (seed->keypair (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7)))

(defun test-wallet (vec)
  (format t "wallet V5R1~%")
  (let* ((w (v vec "wallet"))
         (kp (mnemonic->keypair (v w "mnemonic")))
         (wallet (make-wallet-v5r1 kp)))
    (check "mnemonic -> public key" (string= (octets->hex (keypair-public kp)) (v w "publicKey")))
    (check "mnemonic -> seed" (string= (octets->hex (cl-ton::keypair-secret kp)) (v w "seed")))
    (check "keypair does not print secrets"
           (not (search (v w "seed") (princ-to-string kp))))
    (check "wallet id 2147483409" (= (wallet-v5r1-id) 2147483409))
    (check "code cell" (same-cell-p (wallet-v5r1-code) (v w "code")))
    (check "address" (string= (address->string (wallet-address wallet)) (v w "address")))
    (let ((t1 (v vec "walletTransfer")))
      (multiple-value-bind (ext body)
          (wallet-external-message
           wallet :seqno (v t1 "seqno") :valid-until (v t1 "timeout") :deploy t
           :messages (list (cl-ton::make-message-spec
                            :to (parse-address "EQDa4VOnTYlLvDJ0gZjNYm5PXfSmmtL6Vs6A_CZEtXCNICq_")
                            :value (nano 6/5)
                            :body (end-cell (store-uint (begin-cell) 1 32)))))
        (check "signed transfer body matches @ton/ton" (same-cell-p body (v t1 "body")))
        (check "external message with state init" (same-cell-p ext (v vec "walletExternalWithInit")))))
    (check "bad word count rejected"
           (handler-case (progn (mnemonic->keypair "abandon abandon") nil) (ton-error () t)))
    (check "BIP39-only mnemonic rejected (matches @ton/crypto mnemonicValidate)"
           (and (not (v vec "invalidMnemonic" "valid"))
                (handler-case (progn (mnemonic->keypair (v vec "invalidMnemonic" "words")) nil)
                  (ton-error () t))))))

(defun test-wallet-extra (vec)
  (format t "wallet V5R1 (offline-only branches: seed length, seqno getter, list-of-words, password, message cap, wallet-id args)~%")
  (let ((w (v vec "wallet")))
    (check "seed->keypair rejects a seed that isn't 32 bytes"
           (handler-case (progn (seed->keypair (make-array 16 :element-type '(unsigned-byte 8) :initial-element 3)) nil)
             (ton-error () t)))
    ;; WALLET-SEQNO itself (as opposed to CHAIN-WALLET-SEQNO, which
    ;; FAKE-CHAIN overrides directly and so never calls this): a GETTER
    ;; that succeeds vs. one that signals (an undeployed wallet, in
    ;; TONLIB-CHAIN's real use) -- 0 either way lets a fresh wallet's
    ;; first message still get built.
    (let* ((kp (mnemonic->keypair (v w "mnemonic")))
           (wallet (make-wallet-v5r1 kp)))
      (check "wallet-seqno returns the getter's own answer when it succeeds"
             (= 7 (wallet-seqno (lambda (addr method args) (declare (ignore addr method args)) (list 7)) wallet)))
      (check "wallet-seqno is 0 when the getter errors (undeployed wallet)"
             (= 0 (wallet-seqno (lambda (addr method args) (declare (ignore addr method args))
                                  (error "account not found"))
                                wallet))))
    ;; MNEMONIC->KEYPAIR: a list of words (not just a whitespace string),
    ;; and a non-empty password, which skips the checksum check entirely
    ;; (is_basic_seed only applies to the empty-password derivation) and
    ;; must derive a DIFFERENT key than the same words with no password.
    (let ((words (uiop:split-string (v w "mnemonic") :separator '(#\Space))))
      (check "mnemonic->keypair accepts a list of words, same result as the string form"
             (equalp (keypair-public (mnemonic->keypair words)) (keypair-public (mnemonic->keypair (v w "mnemonic"))))))
    (check "a passworded mnemonic derives a different key than the same words with no password"
           (not (equalp (keypair-public (mnemonic->keypair (v w "mnemonic") :password "hunter2"))
                        (keypair-public (mnemonic->keypair (v w "mnemonic"))))))
    (check "a passworded mnemonic skips the checksum check (garbage 24 words still derive a key)"
           (keypair-public (mnemonic->keypair (v vec "invalidMnemonic" "words") :password "anything")))
    ;; WALLET-EXTERNAL-MESSAGE's own message-count cap
    (let* ((kp (mnemonic->keypair (v w "mnemonic")))
           (wallet (make-wallet-v5r1 kp))
           (one-spec (cl-ton::make-message-spec :to (fake-address #xAA) :value (nano 1)
                                                :body (end-cell (begin-cell)))))
      (check "wallet-external-message refuses more than 255 messages in one go"
             (handler-case (progn (wallet-external-message wallet :seqno 0
                                                           :messages (make-list 256 :initial-element one-spec))
                                  nil)
               (ton-error () t)))
      (check "255 messages is still fine (the boundary itself isn't rejected)"
             (wallet-external-message wallet :seqno 0 :messages (make-list 255 :initial-element one-spec))))
    ;; WALLET-FROM-MNEMONIC (cl-ton's own, distinct from ton-trader's
    ;; LOAD-WALLET wrapper): errors with no mnemonic, else sets *WALLET*.
    (check "wallet-from-mnemonic refuses a NIL mnemonic"
           (handler-case (progn (wallet-from-mnemonic nil) nil) (ton-error () t)))
    (let ((saved *wallet*))
      (unwind-protect
           (progn
             (wallet-from-mnemonic (v w "mnemonic"))
             (check "wallet-from-mnemonic sets *wallet*, address matches the vector"
                    (string= (address->string (wallet-address *wallet*)) (v w "address"))))
        (setf *wallet* saved)))
    ;; WALLET-V5R1-ID: non-default network/workchain/subwallet actually
    ;; change the id, not just the mainnet default the main wallet test covers.
    (check "wallet-v5r1-id: testnet global id differs from mainnet's"
           (/= (wallet-v5r1-id :network-global-id cl-ton::+testnet-global-id+) (wallet-v5r1-id)))
    (check "wallet-v5r1-id: a non-zero subwallet differs from subwallet 0"
           (/= (wallet-v5r1-id :subwallet 7) (wallet-v5r1-id)))
    (check "wallet-v5r1-id: workchain -1 differs from workchain 0"
           (/= (wallet-v5r1-id :workchain -1) (wallet-v5r1-id)))))

(defun test-emulator-real-getter ()
  "RUN-GET-METHOD-LOCAL / EMULATOR-VERSION against the REAL libemulator.so --
FAKE-CHAIN's own CHAIN-EMULATE bypasses the native library entirely (a
scripted result, no FFI call at all), so these are the only real calls
into it anywhere in the offline suite.  No network needed: running a
get-method against code+data cells given directly is pure local TVM
execution, the same as TONLIB.LISP's real getter does after fetching them
from a liteserver -- this exercises exactly that FFI path, just fed cells
built locally instead of fetched remotely."
  (format t "emulator (real libemulator.so: emulator-version, run-get-method-local)~%")
  (load-emulator-library (or (%lib "libemulator-linux-x86_64.so")
                             (error "libemulator-linux-x86_64.so not found (cl-ton/lib/ or <bin>/lib/)")))
  (check "emulator-version returns a non-empty string from the real library"
         (let ((v (emulator-version))) (and (stringp v) (plusp (length v)))))
  (let* ((kp (seed->keypair (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7)))
         (code (wallet-v5r1-code))
         ;; the same data layout MAKE-WALLET-V5R1 builds, by hand, so CODE
         ;; and DATA can be handed to RUN-GET-METHOD-LOCAL directly without
         ;; a STATE-INIT-CODE/-DATA accessor (STATE-INIT is just a cell)
         (data (build-cell (store-bit 1) (store-uint 0 32) (store-int (wallet-v5r1-id) 32)
                           (store-bytes (keypair-public kp)) (store-bit 0))))
    (multiple-value-bind (items exit-code gas missing) (run-get-method-local code data "seqno" nil)
      (check "a fresh (seqno 0) wallet's real seqno getter returns 0"
             (equal items '(0)))
      (check "exit code 0, no missing library" (and (eql exit-code 0) (null missing)))
      (check "gas-used is a positive integer" (and (integerp gas) (plusp gas))))
    (multiple-value-bind (items exit-code) (run-get-method-local code data "get_public_key" nil)
      (check "the real get_public_key getter returns the actual key we put in DATA"
             (and (eql exit-code 0) (equal items (list (octets->uint (keypair-public kp)))))))
    (check "an unknown method id is a normal (non-zero exit-code) VM result, not a crash"
           (multiple-value-bind (items exit-code) (run-get-method-local code data "no_such_method_xyz" nil)
             (declare (ignore items))
             (/= exit-code 0)))))

(defun test-vm-stack ()
  (format t "vm stack~%")
  (let* ((cell (end-cell (store-uint (begin-cell) #xabcd 16)))
         (items (list 0 -1 (expt 2 200) (- (expt 2 255)) cell (stack-slice cell) (stack-null)))
         (back (parse-vm-stack (serialize-vm-stack items))))
    (check "round trip length" (= (length back) (length items)))
    (check "ints" (equal (subseq back 0 4) (subseq items 0 4)))
    (check "cell" (node-equal (nth 4 back) cell))
    (check "slice" (and (slice-p (nth 5 back)) (= #xabcd (load-uint (nth 5 back) 16))))
    (check "null" (eq (nth 6 back) :null))
    (check "empty stack" (null (parse-vm-stack (serialize-vm-stack '()))))
    (check "json int" (equal (cl-ton::json->stack-item
                              (jonathan:parse "{\"@type\":\"tvm.stackEntryNumber\",\"number\":{\"@type\":\"tvm.numberDecimal\",\"number\":\"-42\"}}"
                                              :as :hash-table))
                             -42))))

(defun test-tonlib-dispatch ()
  (format t "tonlib dispatch~%")
  (let* ((tl (cl-ton::%make-tonlib (cffi:null-pointer)))
         (waiter (cl-ton::make-tonlib-waiter)))
    (setf (gethash "req-1" (cl-ton::tonlib-waiters tl)) waiter)
    (cl-ton::dispatch-tonlib-response
     tl "{\"@type\":\"ok\",\"@extra\":\"req-1\",\"value\":42}")
    (check "response correlated by @extra"
           (and (cl-ton::tonlib-waiter-done-p waiter)
                (= 42 (cl-ton::json-get
                       (cl-ton::tonlib-waiter-response waiter) "value"))))
    (check "completed waiter removed"
           (zerop (hash-table-count (cl-ton::tonlib-waiters tl))))
    (cl-ton::dispatch-tonlib-response tl "{\"@type\":\"updateSyncState\"}")
    (check "unsolicited update ignored"
           (zerop (hash-table-count (cl-ton::tonlib-waiters tl)))))
  (let ((waiter (cl-ton::make-tonlib-waiter)))
    (check "timed waiter returns cleanly without retaining its mutex"
           (not (cl-ton::wait-for-tonlib-waiter
                 waiter
                 (+ (get-internal-real-time)
                    (/ internal-time-units-per-second 100)))))))

(defparameter *minimal-global-config-json*
  "{\"@type\":\"config.global\",\"dht\":{\"@type\":\"dht.config.global\",\"k\":6,\"a\":3,\"static_nodes\":{\"@type\":\"dht.nodes\",\"nodes\":[]}},\"liteservers\":[{\"ip\":84478511,\"port\":19949,\"id\":{\"@type\":\"pub.ed25519\",\"key\":\"n4VDnSCUuSpjnCyUk9e3QOOd6o0ItSWYbTnW3Wnn8wk=\"}}],\"validator\":{\"@type\":\"validator.config.global\",\"zero_state\":{\"workchain\":-1,\"shard\":-9223372036854775808,\"seqno\":0,\"root_hash\":\"F6OpKZKqvqeFp6CQmFomXNMfMj2EnaUSOXN+Mh+wVWk=\",\"file_hash\":\"XplPz01CXAps5qeSWUtxcyBfdAo5zVb1N979KLSKD24=\"}}}"
  "Just enough of a real global config's shape (one real liteserver entry,
an empty DHT node list, a real mainnet zerostate) for PROXY-LITESERVER to
parse, accept, and write its own identity against -- this cross-check
never needs that liteserver to actually answer, only to be well-formed
JSON in the shape PROXY-LITESERVER itself expects, so it doesn't need
ton-trader's own global.config.json (a sibling project, not a dependency)
or any network access.")

;;; A released binary that is PRESENT can still be UNRUNNABLE -- the shipped fift and
;;; proxy-liteserver are AppImages, which need libgcc_s.so.1 (and a few more system
;;; libraries) from the host; minimal containers lack it and the dynamic loader fails
;;; before main().  Such a binary is reported once, by name and reason, and treated as
;;; absent (so its legs skip cleanly instead of failing or aborting the suite).
(defvar *binary-runs-cache* (make-hash-table :test #'equal))

(defun binary-runs-p (path)
  "True when PATH starts under the dynamic loader (any exit status); NIL, after printing the
loader's complaint once, when it dies on a missing shared library."
  (multiple-value-bind (known hit) (gethash path *binary-runs-cache*)
    (if hit
        known
        (setf (gethash path *binary-runs-cache*)
              (multiple-value-bind (out err)
                  (handler-case (uiop:run-program (list path "--help") :output '(:string) :error-output '(:string)
                                                                       :ignore-error-status t)
                    (error (e) (values "" (princ-to-string e))))
                (let ((text (concatenate 'string (or out "") (or err ""))))
                  (cond ((or (search "error while loading shared libraries" text)
                             (search "cannot open shared object file" text)
                             (search "fusermount" text)
                             (search "FUSE setup" text))
                         (format t "  note ~A cannot run on this host: ~A~%"
                                 path (let ((line (find-if (lambda (l) (plusp (length (string-trim " " l))))
                                                           (uiop:split-string text :separator '(#\Newline)))))
                                        (string-trim " " (or line ""))))
                         (format t "       missing library or FUSE (AppImage): install libgcc-s1 / fuse, or use ~
                                    bin/tests/run-tests.sh, whose fift/proxy-liteserver are extracted AppImages~%")
                         nil)
                        (t t))))))))

(defun find-proxy-liteserver-binary ()
  "Path to TON's own proxy-liteserver executable: BUNDLED-ENV-BINARY first
(cl-ton/tests/proxy-liteserver-linux-x86_64, or whatever BUILDER.LISP
deployed -- see cl-ton/src/files.lisp), then TON_PROXY_LITESERVER_BINARY
for a manual override. NIL if neither resolves, in which case the
proxy-liteserver cross-check below is skipped, not failed."
  (let ((path (or (cl-ton::bundled-env-binary "proxy-liteserver")
                  (let ((p (uiop:getenv "TON_PROXY_LITESERVER_BINARY")))
                    (and p (probe-file p) p)))))
    (and path (binary-runs-p path) path)))

(defun eventually-not-alive-p (proxy &key (timeout 3))
  "True once PROXY reports not-alive, polling briefly rather than checking
a single instant -- OS-level reaping of a just-terminated process can lag
under heavy CPU load (e.g. immediately after a large from-scratch
compile) even though CLOSE-PROXY-LITESERVER already waited for it and
escalated to a hard kill; this only accommodates that lag, it does not
mask a process that's still genuinely running after it."
  (loop with deadline = (+ (get-internal-real-time) (* timeout internal-time-units-per-second))
        until (not (cl-ton::proxy-liteserver-alive-p proxy))
        do (when (> (get-internal-real-time) deadline) (return nil))
           (sleep 0.1)
        finally (return t)))

(defun test-bundled-env-binary ()
  (format t "bundled-env-binary (resolver)~%")
  (cl-ton::clear-bundled-env-binary-cache)
  (check "an unknown name resolves to NIL, never an error"
         (null (cl-ton::bundled-env-binary "no-such-binary-xyzzy")))
  (check "the negative result is cached (second call agrees)"
         (null (cl-ton::bundled-env-binary "no-such-binary-xyzzy")))
  (let ((p (cl-ton::bundled-env-binary "proxy-liteserver")))
    (check "proxy-liteserver resolves from cl-ton/tests/ in a checkout"
           (and p (search "proxy-liteserver" (file-namestring p))))
    (check "resolution is cached and stable"
           (equal p (cl-ton::bundled-env-binary "proxy-liteserver"))))
  (check "fift resolves from cl-ton/tests/ in a checkout"
         (let ((p (cl-ton::bundled-env-binary "fift"))) (and p (search "fift" (file-namestring p)))))
  ;; In a DEPLOYED build (built by builder.lisp) the checkout no longer exists
  ;; for ASDF, so the only way these resolve is the <bin>/env/ branch.
  (when (and (find-package :deploy)
             (funcall (find-symbol "DEPLOYED-P" :deploy)))
    (let ((dir (namestring (funcall (find-symbol "RUNTIME-DIRECTORY" :deploy))))
          (p (cl-ton::bundled-env-binary "proxy-liteserver")))
      (check "deployed build: proxy-liteserver resolves from <bin>/env/ or beside the binary"
             (and p (uiop:string-prefix-p dir (namestring (truename p)))))
      (check "deployed build: fift resolves from <bin>/env/ or beside the binary"
             (let ((f (cl-ton::bundled-env-binary "fift")))
               (and f (uiop:string-prefix-p dir (namestring (truename f))))))))
  (check "env var name follows the TON_<NAME>_BINARY convention"
         (equal (cl-ton::%env-binary-var-name "proxy-liteserver") "TON_PROXY_LITESERVER_BINARY")))

(defun test-proxy-liteserver-cross-check ()
  "PROXY-LITESERVER.LISP against the real proxy-liteserver binary: launch,
identity round-trip, the generated single-entry config's shape, and that
an existing db's identity survives a restart. Skipped when
TON_PROXY_LITESERVER_BINARY isn't set. Never exercises an actual query
through it -- that needs the real liteservers it would proxy to be
reachable, which no offline test can assume."
  (format t "proxy-liteserver (real TON binary: launch, identity, restart)~%")
  (let ((binary (find-proxy-liteserver-binary)))
    (if (not binary)
        (skip-missing "proxy-liteserver cross-check (TON_PROXY_LITESERVER_BINARY not set)")
        (let* ((tmp (uiop:temporary-directory))
               (db (merge-pathnames (format nil "cl-ton-proxy-ls-~A/" (random most-positive-fixnum)) tmp))
               (config-path (merge-pathnames (format nil "cl-ton-proxy-ls-config-~A.json" (random most-positive-fixnum)) tmp)))
          (with-open-file (s config-path :direction :output :if-exists :supersede)
            (write-string *minimal-global-config-json* s))
          (unwind-protect
               (let ((proxy (cl-ton::open-proxy-liteserver
                             :binary binary :global-config config-path :db db :port 25321 :ready-timeout 15)))
                 (unwind-protect
                      (progn
                        (check "launches and reports alive" (cl-ton::proxy-liteserver-alive-p proxy))
                        (check "picks and reports a real port" (and (integerp (cl-ton::proxy-liteserver-port proxy))
                                                                    (plusp (cl-ton::proxy-liteserver-port proxy))))
                        (multiple-value-bind (port id) (cl-ton::read-proxy-liteserver-identity proxy)
                          (check "identity port matches the struct's own"
                                 (eql port (cl-ton::proxy-liteserver-port proxy)))
                          (check "identity id is a real base64 ed25519 key (32 bytes decoded)"
                                 (= 32 (length (base64-decode id)))))
                        (let* ((out (merge-pathnames (format nil "cl-ton-proxy-ls-out-~A.json" (random most-positive-fixnum)) tmp))
                               (written (cl-ton::proxy-liteserver-global-config-path proxy config-path out)))
                          (unwind-protect
                               (let* ((parsed (jonathan:parse (uiop:read-file-string written) :as :hash-table))
                                 (original (jonathan:parse *minimal-global-config-json* :as :hash-table))
                                 (servers (cl-ton::json-get parsed "liteservers")))
                            (check "wrote exactly one liteserver entry" (= 1 (length servers)))
                            (check "that entry points at 127.0.0.1"
                                   (= (cl-ton::json-get (first servers) "ip") (cl-ton::ipv4-string->ip-int "127.0.0.1")))
                            (check "that entry's port matches the running proxy"
                                   (eql (cl-ton::json-get (first servers) "port") (cl-ton::proxy-liteserver-port proxy)))
                            (check "the rest of the original config (validator section) survived untouched"
                                   (string= (jonathan:to-json (cl-ton::json-get original "validator"))
                                            (jonathan:to-json (cl-ton::json-get parsed "validator")))))
                            (ignore-errors (delete-file out)))))
                   (cl-ton::close-proxy-liteserver proxy))
                 (check "reports not alive once closed" (eventually-not-alive-p proxy))
                 ;; restart against the SAME db, no :port -- its first-launch identity must persist
                 (let ((restarted (cl-ton::open-proxy-liteserver
                                   :binary binary :global-config config-path :db db :ready-timeout 15)))
                   (unwind-protect
                        (check "a restart against an existing db keeps its original port"
                               (eql (cl-ton::proxy-liteserver-port proxy) (cl-ton::proxy-liteserver-port restarted)))
                     (cl-ton::close-proxy-liteserver restarted))))
            (ignore-errors (delete-file config-path))
            (ignore-errors (uiop:delete-directory-tree db :validate t)))))))

(defun test-proxy-liteserver-preflight ()
  "VALIDATE-PROXY-LITESERVER-PRECONDITIONS: the three ways OPEN-PROXY-LITESERVER
used to fail either silently (a full READY-TIMEOUT wait) or with a generic
'exited before writing config.json' now fail immediately with a specific
message naming the actual problem.  Prompted by a real report: proxy-liteserver
never wrote its config.json in a deployed environment -- these are the causes
that manifest exactly that way (as opposed to a network-reachability failure,
which happens strictly after the identity is written; see this file's header
comment and PROXY-LITESERVER-CROSS-CHECK above, which proves that ordering
against the real binary)."
  (format t "proxy-liteserver preflight (binary/config/db checked before forking anything)~%")
  (let* ((tmp (uiop:temporary-directory))
         (binary (find-proxy-liteserver-binary))
         (config-path (merge-pathnames (format nil "cl-ton-proxy-preflight-config-~A.json" (random most-positive-fixnum)) tmp)))
    (with-open-file (s config-path :direction :output :if-exists :supersede)
      (write-string *minimal-global-config-json* s))
    ;; 1. binary missing entirely
    (check "a nonexistent binary is refused by name, before any fork"
           (handler-case (progn (cl-ton::validate-proxy-liteserver-preconditions
                                 "/nonexistent/proxy-liteserver" config-path tmp)
                                nil)
             (ton-error (e) (search "does not exist" (princ-to-string e)))))
    ;; 2. binary exists but lost its execute bit -- exactly OPEN-PROXY-LITESERVER's
    ;;    :BINARY should be the resolved path from BUNDLED-ENV-BINARY, so this is
    ;;    what a re-copied/re-extracted bin/env/ without preserved permissions looks
    ;;    like (builder.lisp's deploy hook sets +x on the way in; some copy/unzip
    ;;    tools don't preserve it on the way back out).
    (if (not binary)
        (skip-missing "binary-not-executable check (no proxy-liteserver binary found)")
        (let ((copy (merge-pathnames (format nil "cl-ton-proxy-noexec-~A" (random most-positive-fixnum)) tmp)))
          (unwind-protect
               (progn
                 (uiop:copy-file binary copy)
                 (sb-posix:chmod copy #o644)
                 (check "a non-executable binary names the real problem, not a generic launch failure"
                        (handler-case (progn (cl-ton::validate-proxy-liteserver-preconditions
                                              copy config-path tmp)
                                             nil)
                          (ton-error (e) (search "not executable" (princ-to-string e))))))
            (ignore-errors (delete-file copy)))))
    ;; 3. global-config missing
    (when binary
      (check "a nonexistent global-config is refused"
             (handler-case (progn (cl-ton::validate-proxy-liteserver-preconditions
                                   binary "/nonexistent/global.config.json" tmp)
                                  nil)
               (ton-error (e) (search "global-config" (princ-to-string e))))))
    ;; 4. db directory exists but this process cannot write into it -- e.g. owned by
    ;;    another user, or a read-only bind mount; UIOP:ENSURE-ALL-DIRECTORIES-EXIST
    ;;    alone does not catch this (the directory can already exist and "exist" is
    ;;    all that call checks).
    (cond
      ((not binary) nil)
      ((zerop (sb-posix:getuid))
       ;; root bypasses DAC permission checks, so chmod 555 wouldn't actually
       ;; block root's own write -- this check only means something as a
       ;; non-root user, which is how proxy-liteserver normally runs anyway.
       (format t "  skip directory-not-writable check (running as root; permissions don't apply)~%"))
      (t
       (let ((locked (merge-pathnames (format nil "cl-ton-proxy-locked-~A/" (random most-positive-fixnum)) tmp)))
         (unwind-protect
              (progn
                (ensure-directories-exist locked)
                (sb-posix:chmod locked #o555)
                (check "a directory that exists but isn't writable is refused, not silently retried"
                       (handler-case (progn (cl-ton::validate-proxy-liteserver-preconditions
                                             binary config-path locked)
                                            nil)
                         (ton-error (e) (search "not writable" (princ-to-string e))))))
           (ignore-errors (sb-posix:chmod locked #o755))
           (ignore-errors (uiop:delete-directory-tree locked :validate t))))))
    ;; 5. the good path: nothing here should be an error, and it leaves DB usable
    (when binary
      (let ((ok (merge-pathnames (format nil "cl-ton-proxy-ok-~A/" (random most-positive-fixnum)) tmp)))
        (unwind-protect
             (check "a real binary, a real config, and a writable db directory all pass"
                    (progn (cl-ton::validate-proxy-liteserver-preconditions binary config-path ok) t))
          (ignore-errors (uiop:delete-directory-tree ok :validate t)))))
    (ignore-errors (delete-file config-path))))

(defun test-block-transaction-pagination ()
  (format t "block transaction pagination~%")
  (let ((responses
          (list
           (jonathan:parse
            "{\"incomplete\":true,\"transactions\":[{\"account\":\"A\",\"lt\":\"1\"}]}"
            :as :hash-table)
           (jonathan:parse
            "{\"incomplete\":false,\"transactions\":[{\"account\":\"B\",\"lt\":\"2\"}]}"
            :as :hash-table)))
        (requests nil))
    (let ((transactions
            (cl-ton::collect-block-transactions
             (lambda (request)
               (push request requests)
               (pop responses))
             :block nil)))
      (setf requests (nreverse requests))
      (check "incomplete block transaction pages are joined"
             (equal (mapcar (lambda (tx) (cl-ton::json-get tx "account"))
                            transactions)
                    '("A" "B")))
      (check "transaction pages use the tonlib method name"
             (every (lambda (request)
                      (string= (getf request :|@type|)
                               "blocks.getTransactions"))
                    requests))
      (check "first transaction page has no cursor"
             (= 7 (getf (first requests) :|mode|)))
      (check "next transaction page uses after mode"
             (= 135 (getf (second requests) :|mode|)))
      (check "next transaction page starts after the final prior id"
             (let ((after (getf (second requests) :|after|)))
               (and (equal "A" (getf after :|account|))
                    (equal "1" (getf after :|lt|))))))))

(defun test-base64 ()
  (format t "base64~%")
  (check "standard round trip"
         (let ((bytes (uint->octets #x0011223344556677 8)))
           (equalp bytes (base64-decode (base64-encode bytes)))))
  (check "url round trip"
         (let ((bytes (uint->octets #xdeadbeefcafebabe 8)))
           (equalp bytes (base64-decode (base64-encode bytes :url t)))))
  (check "known vector: 'Man' -> 'TWFu'" (string= (base64-encode (octets #x4d #x61 #x6e)) "TWFu"))
  (check "known vector decode: 'TWFu' -> 'Man'" (equalp (base64-decode "TWFu") (octets #x4d #x61 #x6e)))
  (check "padding omitted with :pad nil" (string= (base64-encode (octets #x4d) :pad nil) "TQ"))
  (check "unpadded decode matches padded decode" (equalp (base64-decode "TQ") (base64-decode "TQ==")))
  (check "cell round trip through base64 BOC"
         (let ((c (end-cell (store-uint (begin-cell) #xcafef00d 32))))
           (node-equal c (base64->cell (cell->base64 c)))))
  (check "invalid character rejected"
         (handler-case (progn (base64-decode "!!!!") nil) (ton-error () t))))

(defun test-slice ()
  (format t "slice~%")
  (let* ((c (end-cell (let* ((b (store-uint (begin-cell) 5 8))
                             (b (store-int b -5 8))
                             (b (store-bit b 1))
                             (b (store-ref b (end-cell (store-uint (begin-cell) 42 8))))
                             (b (store-ref b (end-cell (store-uint (begin-cell) 43 8)))))
                        b)))
         (s0 (cell-slice c)))
    (check "remaining bits/refs before reading"
           (and (= 17 (slice-remaining-bits s0)) (= 2 (slice-remaining-refs s0))))
    (multiple-value-bind (u s1) (load-uint s0 8)
      (check "load-uint" (= u 5))
      (multiple-value-bind (i s2) (load-int s1 8)
        (check "load-int negative" (= i -5))
        (multiple-value-bind (b s3) (load-bit s2)
          (check "load-bit" (eq b t))
          (check "not empty with two refs left" (not (slice-empty-p s3)))
          (multiple-value-bind (r1 s4) (load-ref s3)
            (check "load-ref first" (= 42 (cell-uint r1 0 8)))
            (multiple-value-bind (r2 s5) (load-ref s4)
              (check "load-ref second" (= 43 (cell-uint r2 0 8)))
              (check "empty after consuming everything" (slice-empty-p s5))
              (check "load-uint underflow signals"
                     (handler-case (progn (load-uint s5 1) nil) (ton-error () t)))
              (check "load-ref underflow signals"
                     (handler-case (progn (load-ref s5) nil) (ton-error () t)))))))))
  (check "load-maybe-ref: absent"
         (null (nth-value 0 (load-maybe-ref (cell-slice (end-cell (store-bit (begin-cell) 0)))))))
  (check "load-maybe-ref: present"
         (let* ((inner (end-cell (store-uint (begin-cell) 99 8)))
                (outer (end-cell (store-ref (store-bit (begin-cell) 1) inner))))
           (= 99 (cell-uint (nth-value 0 (load-maybe-ref (cell-slice outer))) 0 8))))
  (check "slice-rest-bits"
         (multiple-value-bind (val n) (slice-rest-bits (cell-slice (end-cell (store-uint (begin-cell) #b101 3))))
           (and (= n 3) (= val #b101)))))

(defun test-shard-prefix ()
  (format t "shard prefix matching~%")
  (flet ((shard (wc s)
           (let ((h (make-hash-table :test #'equal)))
             (setf (gethash "workchain" h) wc (gethash "shard" h) s)
             h)))
    (let ((addr (fake-address #x11)))    ; top bit of hash byte #x11 (00010001) is 0
      (check "root shard (mask 0) matches everything"
             (cl-ton::shard-includes-address-p (shard 0 #x8000000000000000) addr))
      (check "prefix-0 half matches an address whose top hash bit is 0"
             (cl-ton::shard-includes-address-p (shard 0 #x4000000000000000) addr))
      (check "prefix-1 half does not match"
             (not (cl-ton::shard-includes-address-p (shard 0 #xC000000000000000) addr)))
      (check "wrong workchain never matches"
             (not (cl-ton::shard-includes-address-p (shard 1 #x8000000000000000) addr)))
      (check "decimal-string shard id is accepted"
             (cl-ton::shard-includes-address-p (shard 0 "9223372036854775808") addr)))))

(defun test-flow-event-plumbing ()
  (format t "flow event plumbing~%")
  (flet ((tx-with (account)
           (let ((h (make-hash-table :test #'equal))) (setf (gethash "account" h) account) h)))
    (let ((p1 (fake-address #x51)) (p2 (fake-address #x52)))
      (check "tx-account-hash: address object" (equalp (address-hash p1) (cl-ton::tx-account-hash (tx-with p1))))
      (check "tx-account-hash: friendly-string address"
             (equalp (address-hash p1) (cl-ton::tx-account-hash (tx-with (address->string p1)))))
      (check "watched-pool-for-transaction finds by hash"
             (eq p2 (cl-ton::watched-pool-for-transaction (list p1 p2) (tx-with p2))))
      (check "watched-pool-for-transaction: no match"
             (null (cl-ton::watched-pool-for-transaction (list p1) (tx-with p2))))))
  (let ((scanner (cl-ton::%make-flow-scanner nil nil)))
    (cl-ton::publish-flow-event scanner (cl-ton::make-flow-event :pool :a))
    (cl-ton::publish-flow-event scanner (cl-ton::make-flow-event :pool :b))
    (let ((drained (cl-ton::drain-flow-events scanner)))
      (check "drain returns events oldest-first" (equal (mapcar #'cl-ton::flow-event-pool drained) '(:a :b)))
      (check "drain empties the queue" (null (cl-ton::drain-flow-events scanner))))))

(defun fift-binary ()
  "Path to the fift interpreter: BUNDLED-ENV-BINARY first (the copy
cl-ton/tests/ ships, or whatever BUILDER.LISP deployed alongside it -- see
cl-ton/src/files.lisp), then TON_FIFT_BINARY for a manual override. NIL
if neither resolves. Only fift's own built-in kernel words are used below
(<b, u,, i,, ref,, b>, hash, boc+>B) -- none of this needs Fift.fif/Asm.fif,
which this environment doesn't have either."
  (let ((path (or (cl-ton::bundled-env-binary "fift")
                  (let ((p (uiop:getenv "TON_FIFT_BINARY")))
                    (and p (probe-file p) p)))))
    (and path (binary-runs-p path) path)))

(defun run-fift-script (fift script)
  "Runs SCRIPT (fift source, kernel words only) with `fift -n -s`
(-n skips the standard preamble, which needs Fift.fif) and returns its
stdout, trimmed."
  (let ((path (merge-pathnames (format nil "cl-ton-fift-~A.fif" (random most-positive-fixnum))
                               (uiop:temporary-directory))))
    (unwind-protect
        (progn
          (with-open-file (s path :direction :output :if-exists :supersede) (write-string script s))
          (multiple-value-bind (output error-output code)
              (uiop:run-program (list fift "-n" "-s" (namestring path))
                                :output '(:string) :error-output '(:string) :ignore-error-status t)
            (unless (zerop code) (format t "       fift: ~A~%" error-output))
            (string-trim '(#\Space #\Newline #\Return) output)))
      (ignore-errors (delete-file path)))))

(defun test-ton-boc-fift-cross-check ()
  "Independent verification of CELL-HASH-HEX/SERIALIZE-BOC/PARSE-BOC against
the real fift interpreter's own built-in cell/BOC words -- not another
implementation of the same algorithm, the reference implementation itself.
Skipped when TON_FIFT_BINARY isn't set."
  (format t "ton-boc vs. real fift kernel (cell hashing, BOC serialization)~%")
  (let ((fift (fift-binary)))
    (if (not fift)
        (skip-missing "ton-boc/fift cross-check (TON_FIFT_BINARY not set)")
        (progn
          (check "flat cell hash matches fift's own hash word"
                 (string-equal
                  (cell-hash-hex (end-cell (store-uint (begin-cell) 42 8)))
                  (run-fift-script fift "<b 42 8 u, b> hash x. cr")))
          (check "single-ref cell hash matches fift"
                 (string-equal
                  (cell-hash-hex (end-cell (store-ref (store-uint (begin-cell) 7 3)
                                                      (end-cell (store-uint (begin-cell) 99 8)))))
                  (run-fift-script fift "<b 7 3 u, <b 99 8 u, b> ref, b> hash x. cr")))
          (check "two-ref cell (unsigned + signed children) hash matches fift"
                 (string-equal
                  (cell-hash-hex (end-cell (store-ref (store-ref (store-uint (begin-cell) 5 4)
                                                                  (end-cell (store-uint (begin-cell) 111 8)))
                                                       (end-cell (store-int (begin-cell) -3 8)))))
                  (run-fift-script fift
                                   "<b 5 4 u, <b 111 8 u, b> ref, <b -3 8 i, b> ref, b> hash x. cr")))
          (check "SERIALIZE-BOC bytes match fift's own boc+>B"
                 (string-equal
                  (octets->hex (serialize-boc (end-cell (store-uint (begin-cell) 42 8))))
                  (run-fift-script fift "<b 42 8 u, b> 2 boc+>B Bx. cr")))
          (check "PARSE-BOC reads fift's own BOC output back correctly"
                 (let* ((boc-hex (run-fift-script fift "<b 42 8 u, b> 2 boc+>B Bx. cr"))
                        (parsed (first (parse-boc (hex->octets boc-hex)))))
                   (and (= 42 (cell-uint parsed 0 8))
                        (string-equal (cell-hash-hex parsed)
                                      (run-fift-script fift "<b 42 8 u, b> hash x. cr")))))))))

(defun test-wallet-mnemonic-env ()
  (format t "wallet-from-mnemonic-source (env var wiring)~%")
  (let* ((words (v (vectors) "wallet" "mnemonic"))
         (old-env (sb-ext:posix-getenv "TON_MNEMONIC"))
         (old-file (sb-ext:posix-getenv "TON_MNEMONIC_FILE")))
    (flet ((expected-address ()
             (address->string (wallet-address (make-wallet-v5r1 (mnemonic->keypair words))))))
      (unwind-protect
          (progn
            (sb-posix:unsetenv "TON_MNEMONIC")
            (sb-posix:unsetenv "TON_MNEMONIC_FILE")
            (check "neither var set: returns nil" (null (wallet-from-mnemonic-source)))
            (sb-posix:setenv "TON_MNEMONIC" words 1)
            (check "TON_MNEMONIC read directly"
                   (string= (address->string (wallet-address (wallet-from-mnemonic-source)))
                            (expected-address)))
            (sb-posix:unsetenv "TON_MNEMONIC")
            (let ((path (merge-pathnames "cl-ton-test-mnemonic.tmp" (uiop:temporary-directory))))
              (unwind-protect
                  (progn
                    (with-open-file (s path :direction :output :if-exists :supersede) (write-string words s))
                    (sb-posix:setenv "TON_MNEMONIC_FILE" (namestring path) 1)
                    (check "TON_MNEMONIC_FILE read from file"
                           (string= (address->string (wallet-address (wallet-from-mnemonic-source)))
                                    (expected-address))))
                (ignore-errors (delete-file path))))
            (sb-posix:unsetenv "TON_MNEMONIC_FILE")
            (sb-posix:setenv "TON_MNEMONIC_FILE" "/nonexistent/should-not-exist" 1)
            (check "missing TON_MNEMONIC_FILE errors clearly"
                   (handler-case (progn (wallet-from-mnemonic-source) nil) (ton-error () t))))
        (if old-env (sb-posix:setenv "TON_MNEMONIC" old-env 1) (sb-posix:unsetenv "TON_MNEMONIC"))
        (if old-file (sb-posix:setenv "TON_MNEMONIC_FILE" old-file 1) (sb-posix:unsetenv "TON_MNEMONIC_FILE"))))))

(defun test-transaction-parse ()
  (format t "transaction summary~%")
  ;; Build a minimal Transaction prefix and check total_fees / outmsg_cnt decoding.
  (let* ((tx (end-cell
              (let* ((b (store-uint (begin-cell) #b0111 4))
                     (b (store-uint b 0 256)) (b (store-uint b 5 64))
                     (b (store-uint b 0 256)) (b (store-uint b 4 64)) (b (store-uint b 1700000000 32))
                     (b (store-uint b 2 15)) (b (store-uint b 2 2)) (b (store-uint b 2 2))
                     (b (store-ref b (end-cell (begin-cell))))
                     (b (store-coins b 123456789)))
                b))))
    (multiple-value-bind (fees count) (cl-ton::parse-transaction-summary tx)
      (check "total_fees" (= fees 123456789))
      (check "outmsg_cnt" (= count 2)))))

;;; --- message/transaction parsing used by the cycle tracker ---------------

(defun test-flow-event-backlog ()
  (format t "flow scanner event backlog is bounded~%")
  (let ((scanner (cl-ton::%make-flow-scanner nil nil))
        (*flow-event-backlog* 50))
    (dotimes (i 120)
      (publish-flow-event scanner (cl-ton::make-flow-event :observed-at i)))
    (let ((events (drain-flow-events scanner)))
      (check "only the newest 50 of 120 are kept" (= 50 (length events)))
      (check "the oldest were dropped, order is oldest first"
             (and (= 70 (flow-event-observed-at (first events)))
                  (= 119 (flow-event-observed-at (car (last events)))))))
    (check "a drained scanner starts empty again" (null (drain-flow-events scanner)))
    (check "draining a missing scanner is a no-op" (null (drain-flow-events nil)))))

(defun test-transaction-messages ()
  (format t "transaction messages (dict walk, message envelope, broadcast matching)~%")
  (let* ((dest (fake-address #x21))
         (body (end-cell (store-uint (begin-cell) #xC0FFEE 32)))
         (leaf (lambda (n) (end-cell (store-uint (begin-cell) n 16)))))
    ;; HashmapE 15 ^Cell: 1, 2 and 9 entries exercise short/long/same labels
    (dolist (keys '((0) (0 1 2) (0 1 2 3 4 5 6 7 8) (5 4000 32767)))
      (let* ((entries (loop for k in keys for i from 1
                            collect (cons k (let ((c (funcall leaf i))) (lambda (b) (store-ref b c))))))
             (root (cl-ton::hashmap-cell entries 15))
             (walked (dict-entries root 15 (lambda (v) (values (load-ref v))))))
        (check (format nil "dict walk returns all ~D entries in key order" (length keys))
               (and (equal (mapcar #'car walked) (sort (copy-list keys) #'<))
                    (loop for (nil . cell) in walked
                          for i from 1
                          always (equalp (cell-hash cell) (cell-hash (funcall leaf i))))))))
    ;; internal message envelope
    (let* ((msg (internal-message-relaxed :to dest :value 123456789 :body body :bounce t))
           (sum (parse-message-summary msg)))
      (check "internal message: type, dest, value" (and (eq (getf sum :type) :internal)
                                                        (address-equal (getf sum :dest) dest)
                                                        (= (getf sum :value) 123456789)
                                                        (getf sum :bounce)))
      (check "internal message: body unwrapped" (equalp (cell-hash (getf sum :body)) (cell-hash body)))
      ;; a Transaction whose out_msgs holds two messages
      (let* ((msg2 (internal-message-relaxed :to (fake-address #x22) :value 5 :body nil :bounce nil))
             (out (cl-ton::hashmap-cell
                   (list (cons 0 (lambda (b) (store-ref b msg))) (cons 1 (lambda (b) (store-ref b msg2))))
                   15))
             (io (build-cell (store-bit 0) (store-bit 1) (store-ref out)))
             (tx (end-cell
                  (let* ((b (store-uint (begin-cell) #b0111 4))
                         (b (store-uint b 0 256)) (b (store-uint b 5 64))
                         (b (store-uint b 0 256)) (b (store-uint b 4 64)) (b (store-uint b 1700000000 32))
                         (b (store-uint b 2 15)) (b (store-uint b 2 2)) (b (store-uint b 2 2))
                         (b (store-ref b io))
                         (b (store-coins b 1)))
                    b))))
        (multiple-value-bind (in outs) (transaction-messages tx)
          (check "transaction: no in_msg" (null in))
          (check "transaction: two out messages, in order"
                 (and (= 2 (length outs))
                      (address-equal (getf (parse-message-summary (first outs)) :dest) dest)
                      (= 5 (getf (parse-message-summary (second outs)) :value))))
          (check "transaction: out message without body parses" (null (ignore-errors (cell-bits (getf (parse-message-summary (second outs)) :body)) nil)))))
      (check "emulation-out-message-cells reads a result's transaction"
             (let ((io (build-cell (store-bit 0) (store-bit 1)
                                   (store-ref (cl-ton::hashmap-cell
                                               (list (cons 0 (lambda (b) (store-ref b msg)))) 15)))))
               (= 1 (length (emulation-out-message-cells
                             (cl-ton::make-emulation-result
                              :success-p t
                              :transaction (end-cell
                                            (let* ((b (store-uint (begin-cell) #b0111 4))
                                                   (b (store-uint b 0 256)) (b (store-uint b 5 64))
                                                   (b (store-uint b 0 256)) (b (store-uint b 4 64))
                                                   (b (store-uint b 1700000000 32))
                                                   (b (store-uint b 1 15)) (b (store-uint b 2 2))
                                                   (b (store-uint b 2 2)) (b (store-ref b io))
                                                   (b (store-coins b 1)))
                                              b))))))))
      (check "failed emulation has no out messages"
             (null (emulation-out-message-cells (cl-ton::make-emulation-result :success-p nil)))))
    ;; external message envelope + the identities a broadcast is matched on
    (let* ((ext (external-message :to dest :body body))
           (sum (parse-message-summary ext))
           (norm (external-message-normalized-hash dest body)))
      (check "external message: type and dest" (and (eq (getf sum :type) :external-in)
                                                    (address-equal (getf sum :dest) dest)))
      (check "external message: body unwrapped" (equalp (cell-hash (getf sum :body)) (cell-hash body)))
      (check "normalized hash is a 32-byte digest, stable, and body-sensitive"
             (and (= 32 (length norm))
                  (equalp norm (external-message-normalized-hash dest body))
                  (not (equalp norm (external-message-normalized-hash
                                     dest (end-cell (store-uint (begin-cell) 1 8)))))))
      (flet ((tx (&key hash body-hash)
               (let ((h (make-hash-table :test 'equal)) (m (make-hash-table :test 'equal)))
                 (setf (gethash "hash" m) hash (gethash "body_hash" m) body-hash (gethash "in_msg" h) m)
                 h)))
        (check "match by the hash chain-send returned"
               (transaction-matches-broadcast-p (tx :hash "abc=") :message-hash "abc="))
        (check "match by normalized hash"
               (transaction-matches-broadcast-p (tx :hash (base64-encode norm)) :normalized-hash norm))
        (check "match by body hash when the envelope hash differs"
               (transaction-matches-broadcast-p (tx :hash "other" :body-hash (base64-encode (cell-hash body)))
                                                :message-hash "abc=" :body-hash (cell-hash body)))
        (check "a different message does not match"
               (not (transaction-matches-broadcast-p
                     (tx :hash (base64-encode (cell-hash (funcall leaf 9)))
                         :body-hash (base64-encode (cell-hash (funcall leaf 8))))
                     :message-hash "abc=" :normalized-hash norm :body-hash (cell-hash body))))
        (check "a transaction with no in_msg identity never matches"
               (not (transaction-matches-broadcast-p (tx) :message-hash "abc=" :body-hash (cell-hash body))))))))

(defun run-tests ()  
  (setf *failures* 0 *checks* 0)  
  ;; 1. the BOC serializer's own self-test  
  (check "cl-ton self-test" (eq t (cl-ton:run-boc-tests)))
  (let ((vec (vectors)))
    (test-coins vec)
    (test-dict vec)
    (test-address vec)
    (test-jetton vec)
    (test-wallet vec)
    (test-wallet-extra vec)
    (test-wallet-mnemonic-env)
    (test-vm-stack)
    (test-emulator-real-getter)
    (test-tonlib-dispatch)
    (test-ton-boc-fift-cross-check)
    (test-bundled-env-binary)
    (test-proxy-liteserver-cross-check)
    (test-proxy-liteserver-preflight)
    (test-block-transaction-pagination)
    (test-transaction-parse)
    (test-transaction-messages)
    (test-flow-event-backlog)
    (test-base64)
    (test-skip-policy)
    (test-tl-adnl-ext)   ; Phase A/B unit tests (tests/tl-adnl-ext.lisp)
    (test-tlapi)         ; typed tonlib API (tests/tlapi.lisp)
    (test-cells)         ; cell levels / pruned branches / Merkle proofs (tests/cells.lisp)
    (test-verify)        ; lite proof verification (tests/verify.lisp)
    (test-sync)          ; key-block sync (tests/sync.lisp)
    (test-pmap-conveys)
    (test-lite-client)   ; the verifying liteserver client over ADNL-ext (tests/lite.lisp)
    (test-lite-state-file)   ; its persisted trust state
    (test-lite-commit-key)   ; key blocks kept round by round
    (test-lite-resilience)   ; reconnects, waiting for a block, a state file in use
    (test-lite-backend-parity) ; the lite client as a drop-in for tonlib
    (test-lite-backend-parity-2) ; ... shards, block transactions, raw transactions
    (test-diagnose-lite)     ; the real-network diagnostic, against the fakechain
    (test-proxy-ext)     ; Phase C/D: client + native proxy vs Lisp upstream (tests/proxy-ext.lisp)
    (test-patient-sync)      ; sync keeps going while verified steps arrive
    (test-keystores)         ; private, per-client keystore directories
    (test-network-summary)   ; fast / ok / slow / unknown
    (test-unknown-query-naming)
    (test-proxy-hedging)     ; hedge, adaptive delay, penalties, speed preference, standby
    (test-proxy-scores)      ; upstream speed scores kept across restarts
    (test-proxy-refresh)     ; refreshing the liteserver list
    (test-proxy-connection-stats) ; inbound connection lifecycle + answer times
    (test-proxy-retry)       ; retry on another upstream: stall / drop / pruned / single
    (test-proxy-diagnostics) ; where the native proxy stops: stage, hint, verdict, watch
    (test-proxy-ext-vs-binary)  ; ... vs the released binary (skips without it)
    (test-fakechain)     ; F.1: real tonlib <-> emulator-backed fakechain (tests/fakechain.lisp)
    (test-fakechain-fixtures) ; F.4 seam: capture/replay account fixtures
    (test-fakechain-internal) ; F.1b: internal-message hops, bounce, StateInit deploy
    (test-fakechain-block-transactions) ; liteServer.listBlockTransactions via tonlib blocks.getTransactions
    (test-proxy-inflight-upstream-loss) ; F.2: killed-upstream answers, native == binary
    (test-fakechain-query-faults) ; fail-next / answer-delay
    (test-proxy-scenarios) ; F.3 remainder: watermark, malformed frames
    (test-proxy-lagging-failover) ; lagging liteserver: failover instead of poisoning the client
    (test-proxy-stale-upstream) ; freshness pollers, startup grace
    (test-library-cells) ; library references + getLibraries
    (test-fakechain-library-execution) ; library-code contracts execute once the library is published
    (test-fakechain-faults) ; drop-externals / stall-p
    (test-tonlib-through-flaky-links) ; slow, flaky links between the proxy and the liteservers
    (test-tonlib-via-native-proxy) ; F.3/E: tonlib -> native proxy -> fakechain
    (test-tonlib-via-binary-proxy) ; F.2: same scenario, released binary (skips without it)
    (test-slice)
    (test-shard-prefix)
    (test-flow-event-plumbing)
    (run-execution-tests))
  (format t "~&~D checks, ~D failures~%" *checks* *failures*)  
  (when (plusp *failures*) (error "~D test~:P failed" *failures*))
  t)
