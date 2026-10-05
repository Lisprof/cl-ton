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

;;;; chain.lisp -- the bot's view of the blockchain as a small protocol.
;;;;
;;;; Execution (execution.lisp) only ever talks to a CHAIN.  TONLIB-CHAIN is
;;;; the real thing (tonlib + libemulator); the test suite provides a fake
;;;; that scripts balances and swap outcomes so the state machine can be
;;;; exercised without a network or a funded wallet.

(in-package :cl-ton)

(defclass chain () ())

(defgeneric chain-pools (chain)
  (:documentation "Fresh POOL-STATE snapshots of all configured pools."))
(defgeneric chain-ton-balance (chain)
  (:documentation "Wallet TON balance in nanoTON."))
(defgeneric chain-usdt-balance (chain)
  (:documentation "Wallet USDT balance in base units; 0 while the jetton wallet is not deployed."))
(defgeneric chain-jetton-balance (chain master)
  (:documentation "The wallet's balance, in base units, of the jetton whose
master contract is MASTER (an ADDRESS); 0 while its jetton wallet is not
deployed.  CHAIN-USDT-BALANCE is the same question for USDT specifically."))
(defgeneric chain-wallet-transactions (chain &key limit)
  (:documentation "The wallet's most recent transactions as raw.transaction
documents (see TRANSACTION-MATCHES-BROADCAST-P), newest first."))
(defgeneric chain-drain-flow-events (chain)
  (:documentation "FLOW-EVENTs the confirmed-flow scanner has seen on the
watched pool addresses since the last drain (oldest first); NIL when this
chain has no scanner.  Advisory only: an event proves a pool processed
SOMETHING, never that it was this bot's message."))
(defgeneric chain-wallet-deployed-p (chain))
(defgeneric chain-wallet-seqno (chain))
(defgeneric chain-send (chain external)
  (:documentation "Broadcast an external message cell; returns its hash."))
(defgeneric chain-emulate (chain external &key pretend-balance)
  (:documentation "EMULATION-RESULT of EXTERNAL against the wallet account."))
(defgeneric chain-now (chain)
  (:documentation "Unix time; fakes may run a virtual clock."))
(defgeneric chain-sleep (chain seconds))
(defgeneric chain-wait-block (chain &key timeout))
(defgeneric chain-set-wallet (chain wallet usdt-wallet))
(defgeneric chain-getter (chain)
  (:documentation "The (address method stack) -> items function, for resolution."))
(defgeneric chain-close (chain))

;;; --- tonlib implementation ---------------------------------------------

(defclass tonlib-chain (chain)
  ((tl :initarg :tl :reader tonlib-chain-tl)
   (getter :initarg :getter :reader chain-getter)
   (dexes :initarg :dexes :reader tonlib-chain-dexes)
   (pool-fetcher :initarg :pool-fetcher :initform nil :reader tonlib-chain-pool-fetcher)
   (wallet :initarg :wallet :accessor tonlib-chain-wallet)
   (usdt-wallet :initarg :usdt-wallet :accessor tonlib-chain-usdt-wallet)
   (head-poller :initarg :head-poller :initform nil :reader tonlib-chain-head-poller)
   (scanner :initarg :scanner :initform nil :accessor tonlib-chain-scanner)
   (proxy :initarg :proxy :initform nil :reader tonlib-chain-proxy) ; PROXY-LITESERVER owned by this chain
   (config-cell :initform nil :accessor tonlib-chain-config-cell)
   (jetton-wallets :initform (make-hash-table :test 'equal) :reader tonlib-chain-jetton-wallets)))

(defun make-tonlib-chain (tl getter dexes wallet usdt-wallet
                          &key head-poller scanner pool-fetcher proxy)
  "POOL-FETCHER is (GETTER DEXES) -> list of pool states, supplied by the
caller: cl-ton itself has no DEX-contract knowledge (see dex.lisp's bare
DEFGENERICs), so CHAIN-POOLS below can't know how to turn opaque DEXES
objects into pool states without it -- the trader passes its own
FETCH-POOL-STATES (dex-config.lisp) when it opens a chain."
  (make-instance 'tonlib-chain :tl tl :getter getter :dexes dexes :pool-fetcher pool-fetcher
                               :wallet wallet :usdt-wallet usdt-wallet
                               :head-poller head-poller :scanner scanner :proxy proxy))

(defmethod chain-pools ((c tonlib-chain))
  (if (tonlib-chain-pool-fetcher c)
      (funcall (tonlib-chain-pool-fetcher c) (chain-getter c) (tonlib-chain-dexes c))
      (ton-error "this chain has no POOL-FETCHER (see MAKE-TONLIB-CHAIN); ~
                  cl-ton has no DEX-contract knowledge of its own to fetch pool states with")))

(defun tonlib-chain-wallet-address (c)
  (wallet-address (or (tonlib-chain-wallet c) (ton-error "no wallet attached"))))

(defmethod chain-ton-balance ((c tonlib-chain))
  (account-state-balance (tonlib-account-state (tonlib-chain-tl c) (tonlib-chain-wallet-address c))))

(defmethod chain-usdt-balance ((c tonlib-chain))
  ;; Network errors propagate so a transient failure is never read as 0.
  (let* ((addr (or (tonlib-chain-usdt-wallet c) (ton-error "no USDT wallet attached")))
         (state (tonlib-account-state (tonlib-chain-tl c) addr)))
    (if (eq (account-state-status state) :active)
        (jetton-wallet-balance (chain-getter c) addr)
        0)))

(defun tonlib-chain-jetton-wallet (c master)
  "The wallet's own jetton wallet for MASTER, derived once per master."
  (let ((key (address->string master))
        (table (tonlib-chain-jetton-wallets c)))
    (or (gethash key table)
        (setf (gethash key table)
              (jetton-wallet-address (chain-getter c) master (tonlib-chain-wallet-address c))))))

(defmethod chain-jetton-balance ((c tonlib-chain) master)
  ;; Network errors propagate so a transient failure is never read as 0.
  (let* ((addr (tonlib-chain-jetton-wallet c master))
         (state (tonlib-account-state (tonlib-chain-tl c) addr)))
    (if (eq (account-state-status state) :active)
        (jetton-wallet-balance (chain-getter c) addr)
        0)))

(defmethod chain-wallet-transactions ((c tonlib-chain) &key (limit 16))
  (let ((txs (tonlib-transactions (tonlib-chain-tl c) (tonlib-chain-wallet-address c))))
    (coerce (subseq txs 0 (min limit (length txs))) 'list)))

(defmethod chain-drain-flow-events ((c tonlib-chain))
  (drain-flow-events (tonlib-chain-scanner c)))

(defmethod chain-wallet-deployed-p ((c tonlib-chain))
  (eq :active (account-state-status
               (tonlib-account-state (tonlib-chain-tl c) (tonlib-chain-wallet-address c)))))

(defmethod chain-wallet-seqno ((c tonlib-chain))
  (wallet-seqno (chain-getter c) (tonlib-chain-wallet c)))

(defmethod chain-send ((c tonlib-chain) external)
  (tonlib-send-message (tonlib-chain-tl c) external))

(defun tonlib-chain-config (c)
  (or (tonlib-chain-config-cell c)
      (setf (tonlib-chain-config-cell c) (tonlib-config-cell (tonlib-chain-tl c)))))

(defmethod chain-emulate ((c tonlib-chain) external &key pretend-balance)
  (let* ((wallet (tonlib-chain-wallet c))
         (shard (if pretend-balance
                    (funded-shard-account (wallet-address wallet) (wallet-state-init wallet) pretend-balance)
                    (tonlib-shard-account-cell (tonlib-chain-tl c) (wallet-address wallet)))))
    (emulate-external-message (tonlib-chain-config c) shard external)))

(defmethod chain-now ((c tonlib-chain)) (unix-now))
(defmethod chain-sleep ((c tonlib-chain) seconds) (sleep seconds))

(defstruct (head-poller (:constructor %make-head-poller (client)))
  client
  (lock (sb-thread:make-mutex :name "masterchain head poller") :read-only t)
  (queue (sb-thread:make-waitqueue :name "masterchain head poller") :read-only t)
  head          ; full ton.blockIdExt of the newest masterchain block
  seqno         ; its seqno, for monotonic comparison
  stop-p
  thread)

(defun publish-head (poller block)  
  (let ((seqno (json-get block "seqno")))  
    (sb-thread:with-mutex ((head-poller-lock poller))  
      (when (or (null (head-poller-seqno poller))  
                (> seqno (head-poller-seqno poller)))  
        (setf (head-poller-head poller) block  
              (head-poller-seqno poller) seqno)  
        (sb-thread:condition-broadcast (head-poller-queue poller))))))

;; (defun publish-head (poller seqno)
;;   (sb-thread:with-mutex ((head-poller-lock poller))
;;     (when (or (null (head-poller-head poller))
;;               (> seqno (head-poller-head poller)))
;;       (setf (head-poller-head poller) seqno)
;;       (sb-thread:condition-broadcast (head-poller-queue poller)))))

(defun start-head-poller (client)
  "Continuously publish increasing masterchain seqnos from CLIENT."
  (let ((poller (%make-head-poller client)))
    (setf (head-poller-thread poller)
          (sb-thread:make-thread
           (lambda ()
             (loop
               (when (sb-thread:with-mutex ((head-poller-lock poller))
                       (head-poller-stop-p poller))
                 (return))
               (handler-case
                   (progn
                     (publish-head poller
                                   (tonlib-masterchain-block client :timeout 3.0d0)) ;;changed info with block
                     (sleep 0.1))
                 (error (e)
                   (warn "head poller: ~A" e)
                   (sleep 0.25)))))
           :name "TON masterchain head poller"))
    poller))

(defun stop-head-poller (poller)
  (when poller
    (sb-thread:with-mutex ((head-poller-lock poller))
      (setf (head-poller-stop-p poller) t)
      (sb-thread:condition-broadcast (head-poller-queue poller)))
    (when (head-poller-thread poller)
      (sb-thread:join-thread (head-poller-thread poller)
                             :default nil :timeout 5))
    ;; Never close the client under a poller thread that is still running.
    (if (and (head-poller-thread poller)
             (sb-thread:thread-alive-p (head-poller-thread poller)))
        (warn "head poller thread did not stop in 5s; leaving its tonlib client open")
        (close-tonlib (head-poller-client poller))))
  nil)

(defun wait-for-published-head (poller baseline-seqno timeout)  
  (let ((deadline (+ (get-internal-real-time)  
                     (* timeout internal-time-units-per-second))))  
    (block wait  
      (sb-thread:with-mutex ((head-poller-lock poller))  
        (loop  
          (let ((seqno (head-poller-seqno poller))  
                (remaining (/ (- deadline (get-internal-real-time))  
                              internal-time-units-per-second)))  
            (when (and seqno (or (null baseline-seqno) (> seqno baseline-seqno)))  
              (return-from wait (head-poller-head poller)))  
            (when (or (head-poller-stop-p poller) (<= remaining 0))  
              (return-from wait nil))  
            (unless (sb-thread:condition-wait  
                     (head-poller-queue poller)  
                     (head-poller-lock poller)  
                     :timeout remaining)  
              (return-from wait nil))))))))

(defmethod chain-wait-block ((c tonlib-chain) &key (timeout 3))  
  (let ((poller (tonlib-chain-head-poller c)))  
    (if poller  
        (let ((baseline  
                (sb-thread:with-mutex ((head-poller-lock poller))  
                  (head-poller-seqno poller))))  
          (wait-for-published-head poller baseline timeout))  
        (let* ((tl (tonlib-chain-tl c))  
               (deadline (+ (get-internal-real-time)  
                            (* timeout internal-time-units-per-second)))  
               (baseline-block  
                 (tonlib-masterchain-block  
                  tl :timeout (coerce (max 0.1 (min timeout 3)) 'double-float)))  
               (baseline (json-get baseline-block "seqno")))  
          (loop  
            for remaining = (/ (- deadline (get-internal-real-time))  
                               internal-time-units-per-second)  
            when (<= remaining 0) return nil  
            do (let* ((block (tonlib-masterchain-block  
                              tl :timeout (coerce (max 0.1 (min 1 remaining)) 'double-float)))  
                      (seqno (json-get block "seqno")))  
                 (when (> seqno baseline) (return block)))  
               (sleep (min 0.1 (max 0 remaining))))))))

;;; --- waiting -------------------------------------------------------------

(defun wait-until (chain predicate timeout &key (interval 3))
  "Poll PREDICATE after each new block, bounded by INTERVAL and TIMEOUT.
Returns the first true value or NIL on timeout."
  (loop with deadline = (+ (chain-now chain) timeout)
        for value = (funcall predicate)
        until value
        do (when (>= (chain-now chain) deadline) (return nil))
           (chain-wait-block chain :timeout interval)
        finally (return value)))

(defmethod chain-set-wallet ((c tonlib-chain) wallet usdt-wallet)
  (setf (tonlib-chain-wallet c) wallet
        (tonlib-chain-usdt-wallet c) usdt-wallet))

(defmethod chain-close ((c tonlib-chain))
  ;; the proxy goes last and even when a close above signals: tonlib clients
  ;; first (they hold sessions to it), and a failed close never leaks the proxy
  (unwind-protect
       (progn
         (when (tonlib-chain-scanner c)
           (stop-flow-scanner (tonlib-chain-scanner c)))
         (stop-head-poller (tonlib-chain-head-poller c))
         (close-tonlib (tonlib-chain-tl c)))
    (close-proxy-liteserver (tonlib-chain-proxy c))))
