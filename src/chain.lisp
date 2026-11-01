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

;;;; chain.lisp -- the bot's view of the blockchain: a structure of operations.
;;;;
;;;; Execution (execution.lisp) only ever talks to a CHAIN.  TONLIB-CHAIN is
;;;; the real thing (tonlib + libemulator); the test suite provides a fake
;;;; that scripts balances and swap outcomes so the state machine can be
;;;; exercised without a network or a funded wallet.  Each is a CHAIN that
;;;; includes this structure and fills in the operation slots.

(in-package :cl-ton)

(defun %chain-op-unsupported (name)
  (lambda (&rest args)
    (declare (ignore args))
    (ton-error "this chain does not support ~A" name)))

(defstruct (chain (:constructor %make-chain) (:copier nil))
  "The bot's view of the blockchain: one FUNCTION per operation, held in the slots, so an implementation (TONLIB-CHAIN, the
test suite's fake) is a CHAIN that includes this structure and fills them in; no generic function dispatch.  Call the
operations through the CHAIN-* functions below, which say what each one does."
  (op-pools (%chain-op-unsupported "chain-pools") :type function)
  (op-ton-balance (%chain-op-unsupported "chain-ton-balance") :type function)
  (op-usdt-balance (%chain-op-unsupported "chain-usdt-balance") :type function)
  (op-jetton-balance (%chain-op-unsupported "chain-jetton-balance") :type function)
  (op-wallet-transactions (%chain-op-unsupported "chain-wallet-transactions") :type function)
  (op-drain-flow-events (constantly nil) :type function)
  (op-wallet-deployed-p (%chain-op-unsupported "chain-wallet-deployed-p") :type function)
  (op-wallet-seqno (%chain-op-unsupported "chain-wallet-seqno") :type function)
  (op-send (%chain-op-unsupported "chain-send") :type function)
  (op-emulate (%chain-op-unsupported "chain-emulate") :type function)
  (op-now #'unix-now :type function)
  (op-sleep #'sleep :type function)
  (op-wait-block (%chain-op-unsupported "chain-wait-block") :type function)
  (op-set-wallet (%chain-op-unsupported "chain-set-wallet") :type function)
  (op-getter (%chain-op-unsupported "chain-getter") :type function)
  (op-close (constantly nil) :type function))

(defun chain-pools (chain)
  "Fresh POOL-STATE snapshots of all configured pools."
  (funcall (chain-op-pools chain)))
(defun chain-ton-balance (chain)
  "Wallet TON balance in nanoTON."
  (funcall (chain-op-ton-balance chain)))
(defun chain-usdt-balance (chain)
  "Wallet USDT balance in base units; 0 while the jetton wallet is not deployed."
  (funcall (chain-op-usdt-balance chain)))
(defun chain-jetton-balance (chain master)
  "The wallet's balance, in base units, of the jetton whose master contract is MASTER (an ADDRESS); 0 while its jetton wallet
is not deployed.  CHAIN-USDT-BALANCE is the same question for USDT specifically."
  (funcall (chain-op-jetton-balance chain) master))
(defun chain-wallet-transactions (chain &key (limit 16))
  "The wallet's most recent transactions as typed raw.transaction documents (see TRANSACTION-MATCHES-BROADCAST-P), newest first."
  (funcall (chain-op-wallet-transactions chain) limit))
(defun chain-drain-flow-events (chain)
  "FLOW-EVENTs the confirmed-flow scanner has seen on the watched pool addresses since the last drain (oldest first); NIL when
this chain has no scanner.  Advisory only: an event proves a pool processed SOMETHING, never that it was this bot's message."
  (funcall (chain-op-drain-flow-events chain)))
(defun chain-wallet-deployed-p (chain)
  (funcall (chain-op-wallet-deployed-p chain)))
(defun chain-wallet-seqno (chain)
  (funcall (chain-op-wallet-seqno chain)))
(defun chain-send (chain external)
  "Broadcast an external message cell; returns its hash."
  (funcall (chain-op-send chain) external))
(defun chain-emulate (chain external &key pretend-balance)
  "EMULATION-RESULT of EXTERNAL against the wallet account."
  (funcall (chain-op-emulate chain) external pretend-balance))
(defun chain-now (chain)
  "Unix time; fakes may run a virtual clock."
  (funcall (chain-op-now chain)))
(defun chain-sleep (chain seconds)
  (funcall (chain-op-sleep chain) seconds))
(defun chain-wait-block (chain &key (timeout 3))
  (funcall (chain-op-wait-block chain) timeout))
(defun chain-set-wallet (chain wallet usdt-wallet)
  (funcall (chain-op-set-wallet chain) wallet usdt-wallet))
(defun chain-getter (chain)
  "The (address method stack) -> items function, for resolution."
  (funcall (chain-op-getter chain)))
(defun chain-close (chain)
  (funcall (chain-op-close chain)))

;;; --- tonlib implementation ---------------------------------------------

(defstruct (tonlib-chain (:include chain) (:constructor %make-tonlib-chain) (:conc-name tonlib-chain-) (:copier nil))
  tl dexes pool-fetcher wallet usdt-wallet head-poller scanner
  proxy                                 ; PROXY-LITESERVER owned by this chain
  (config-cell nil)
  (jetton-wallets (make-hash-table :test 'equal)))

(defun make-tonlib-chain (tl getter dexes wallet usdt-wallet
                          &key head-poller scanner pool-fetcher proxy)
  "POOL-FETCHER is (GETTER DEXES) -> list of pool states, supplied by the
caller: cl-ton itself has no DEX-contract knowledge (see dex.lisp's bare
DEFGENERICs), so CHAIN-POOLS below can't know how to turn opaque DEXES
objects into pool states without it -- the trader passes its own
FETCH-POOL-STATES (dex-config.lisp) when it opens a chain."
  (let ((c (%make-tonlib-chain :tl tl :dexes dexes :pool-fetcher pool-fetcher
                               :wallet wallet :usdt-wallet usdt-wallet
                               :head-poller head-poller :scanner scanner :proxy proxy)))
    (setf (chain-op-pools c) (lambda () (%tonlib-chain-pools c))
          (chain-op-ton-balance c) (lambda () (%tonlib-chain-ton-balance c))
          (chain-op-usdt-balance c) (lambda () (%tonlib-chain-usdt-balance c))
          (chain-op-jetton-balance c) (lambda (master) (%tonlib-chain-jetton-balance c master))
          (chain-op-wallet-transactions c) (lambda (limit) (%tonlib-chain-wallet-transactions c limit))
          (chain-op-drain-flow-events c) (lambda () (%tonlib-chain-drain-flow-events c))
          (chain-op-wallet-deployed-p c) (lambda () (%tonlib-chain-wallet-deployed-p c))
          (chain-op-wallet-seqno c) (lambda () (%tonlib-chain-wallet-seqno c))
          (chain-op-send c) (lambda (external) (%tonlib-chain-send c external))
          (chain-op-emulate c) (lambda (external pretend-balance) (%tonlib-chain-emulate c external pretend-balance))
          (chain-op-wait-block c) (lambda (timeout) (%tonlib-chain-wait-block c timeout))
          (chain-op-set-wallet c) (lambda (wallet usdt-wallet) (%tonlib-chain-set-wallet c wallet usdt-wallet))
          (chain-op-getter c) (lambda () getter)
          (chain-op-close c) (lambda () (%tonlib-chain-close c)))
    c))

(defun %tonlib-chain-pools (c)
  (if (tonlib-chain-pool-fetcher c)
      (funcall (tonlib-chain-pool-fetcher c) (chain-getter c) (tonlib-chain-dexes c))
      (ton-error "this chain has no POOL-FETCHER (see MAKE-TONLIB-CHAIN); ~
                  cl-ton has no DEX-contract knowledge of its own to fetch pool states with")))

(defun tonlib-chain-wallet-address (c)
  (wallet-address (or (tonlib-chain-wallet c) (ton-error "no wallet attached"))))

(defun %tonlib-chain-ton-balance (c)
  (account-state-balance (tonlib-account-state (tonlib-chain-tl c) (tonlib-chain-wallet-address c))))

(defun %tonlib-chain-usdt-balance (c)
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

(defun %tonlib-chain-jetton-balance (c master)
  ;; Network errors propagate so a transient failure is never read as 0.
  (let* ((addr (tonlib-chain-jetton-wallet c master))
         (state (tonlib-account-state (tonlib-chain-tl c) addr)))
    (if (eq (account-state-status state) :active)
        (jetton-wallet-balance (chain-getter c) addr)
        0)))

(defun %tonlib-chain-wallet-transactions (c limit)
  (let ((txs (tonlib-transactions (tonlib-chain-tl c) (tonlib-chain-wallet-address c))))
    (coerce (subseq txs 0 (min limit (length txs))) 'list)))

(defun %tonlib-chain-drain-flow-events (c)
  (drain-flow-events (tonlib-chain-scanner c)))

(defun %tonlib-chain-wallet-deployed-p (c)
  (eq :active (account-state-status
               (tonlib-account-state (tonlib-chain-tl c) (tonlib-chain-wallet-address c)))))

(defun %tonlib-chain-wallet-seqno (c)
  (wallet-seqno (chain-getter c) (tonlib-chain-wallet c)))

(defun %tonlib-chain-send (c external)
  (tonlib-send-message (tonlib-chain-tl c) external))

(defun tonlib-chain-config (c)
  (or (tonlib-chain-config-cell c)
      (setf (tonlib-chain-config-cell c) (tonlib-config-cell (tonlib-chain-tl c)))))

(defun %tonlib-chain-emulate (c external pretend-balance)
  (let* ((wallet (tonlib-chain-wallet c))
         (shard (if pretend-balance
                    (funded-shard-account (wallet-address wallet) (wallet-state-init wallet) pretend-balance)
                    (tonlib-shard-account-cell (tonlib-chain-tl c) (wallet-address wallet)))))
    (emulate-external-message (tonlib-chain-config c) shard external)))


(defstruct (head-poller (:constructor %make-head-poller (client)))
  client
  (lock (sb-thread:make-mutex :name "masterchain head poller") :read-only t)
  (queue (sb-thread:make-waitqueue :name "masterchain head poller") :read-only t)
  head          ; full ton.blockIdExt of the newest masterchain block
  seqno         ; its seqno, for monotonic comparison
  stop-p
  thread)

(defun publish-head (poller block)  
  (let ((seqno (block-id-seqno block)))  
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

(defun %tonlib-chain-wait-block (c timeout)  
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
               (baseline (block-id-seqno baseline-block)))  
          (loop  
            for remaining = (/ (- deadline (get-internal-real-time))  
                               internal-time-units-per-second)  
            when (<= remaining 0) return nil  
            do (let* ((block (tonlib-masterchain-block  
                              tl :timeout (coerce (max 0.1 (min 1 remaining)) 'double-float)))  
                      (seqno (block-id-seqno block)))  
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

(defun %tonlib-chain-set-wallet (c wallet usdt-wallet)
  (setf (tonlib-chain-wallet c) wallet
        (tonlib-chain-usdt-wallet c) usdt-wallet))

(defun %tonlib-chain-close (c)
  ;; the proxy goes last and even when a close above signals: tonlib clients
  ;; first (they hold sessions to it), and a failed close never leaks the proxy
  (unwind-protect
       (progn
         (when (tonlib-chain-scanner c)
           (stop-flow-scanner (tonlib-chain-scanner c)))
         (stop-head-poller (tonlib-chain-head-poller c))
         (close-tonlib (tonlib-chain-tl c)))
    (close-proxy-liteserver (tonlib-chain-proxy c))))
