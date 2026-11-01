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

;;;; tests/fake-chain.lisp -- execution state machine tests on a scripted chain.
;;;;
;;;; FAKE-CHAIN implements the CHAIN protocol with a virtual clock.  Each
;;;; CHAIN-SEND pops the next scripted reaction: a list of (DELAY . EFFECTS)
;;;; applied to the fake balances/seqno as the clock advances, so leg fills,
;;;; DEX refunds, dropped externals and vanished funds can all be replayed
;;;; deterministically and without a network.

(in-package :cl-ton/test)

(defstruct (fake-chain (:include chain) (:constructor %make-fake-chain) (:conc-name fake-) (:copier nil))
  pools
  ton
  (usdt 0)
  (seqno 5)
  (now 1800000000)
  (head 1)
  (block-waits 0)
  (script '())
  (pending '())
  (sent '())
  (emulate-fn (constantly t))
  (pool-hook nil)
  ;; jetton balances by master address string; USDT keeps its own slot.
  (jettons (make-hash-table :test 'equal))
  ;; raw.transaction-shaped documents the wallet "processed", newest first
  (txs '())
  (tx-counter 0)
  ;; FLOW-EVENTs awaiting CHAIN-DRAIN-FLOW-EVENTS (oldest first)
  (flow-events '())
  (wallet-txs-fn nil))

(defun make-fake-chain (&rest initargs)
  "A FAKE-CHAIN (see the keyword slots above) with its CHAIN operations installed."
  (let ((c (apply #'%make-fake-chain initargs)))
    (setf (cl-ton::chain-op-pools c) (lambda () (%fake-chain-pools c))
          (cl-ton::chain-op-ton-balance c) (lambda () (fake-ton c))
          (cl-ton::chain-op-usdt-balance c) (lambda () (fake-usdt c))
          (cl-ton::chain-op-jetton-balance c) (lambda (master) (fake-jetton-balance c master))
          (cl-ton::chain-op-wallet-transactions c) (lambda (limit) (%fake-chain-wallet-transactions c limit))
          (cl-ton::chain-op-drain-flow-events c) (lambda () (%fake-chain-drain-flow-events c))
          (cl-ton::chain-op-wallet-deployed-p c) (constantly t)
          (cl-ton::chain-op-wallet-seqno c) (lambda () (fake-seqno c))
          (cl-ton::chain-op-now c) (lambda () (fake-now c))
          (cl-ton::chain-op-set-wallet c) (lambda (wallet usdt-wallet) (declare (ignore wallet usdt-wallet)))
          (cl-ton::chain-op-getter c) (lambda () (lambda (&rest args) (declare (ignore args)) (error "no getter")))
          (cl-ton::chain-op-close c) (lambda ())
          (cl-ton::chain-op-emulate c) (lambda (external pretend-balance) (%fake-chain-emulate c external pretend-balance))
          (cl-ton::chain-op-send c) (lambda (external) (%fake-chain-send c external))
          (cl-ton::chain-op-sleep c) (lambda (seconds) (%fake-chain-sleep c seconds))
          (cl-ton::chain-op-wait-block c) (lambda (timeout) (%fake-chain-wait-block c timeout)))
    c))

(defun %fake-chain-pools (c)
  (when (fake-pool-hook c) (funcall (fake-pool-hook c) c))
  (fake-pools c))
(defun fake-jetton-balance (c master)
  (gethash (address->string master) (fake-jettons c) 0))
(defun (setf fake-jetton-balance) (value c master)
  (setf (gethash (address->string master) (fake-jettons c)) value))


(defun %fake-chain-wallet-transactions (c limit)
  (when (fake-wallet-txs-fn c) (funcall (fake-wallet-txs-fn c) c))
  (let ((txs (fake-txs c))) (subseq txs 0 (min limit (length txs)))))

(defun %fake-chain-drain-flow-events (c)
  (prog1 (fake-flow-events c) (setf (fake-flow-events c) '())))

(defun make-fake-tx (c hash out-count)
  "A typed raw.transaction consuming the external message whose base64 hash is HASH (a string that is not valid
base64 stands for its own ASCII octets)."
  (let ((octets (or (ignore-errors (base64-decode hash))
                    (map '(vector (unsigned-byte 8)) #'char-code hash))))
    (make-raw-transaction :utime (fake-now c)
                          :lt (incf (fake-tx-counter c))
                          :hash (map '(vector (unsigned-byte 8)) #'char-code "fake-tx")
                          :in-msg (make-raw-message :hash octets
                                                    :body-hash (map '(vector (unsigned-byte 8)) #'char-code
                                                                    "fake-body-hash"))
                          :out-msgs (loop repeat out-count
                                          collect (make-raw-message :source "wallet")))))


(defun %fake-chain-emulate (c external pretend-balance)
  (declare (ignore external pretend-balance))
  (if (funcall (fake-emulate-fn c) c)
      (cl-ton::make-emulation-result :success-p t :fees (nano 1/100))
      (cl-ton::make-emulation-result :success-p nil :error "scripted rejection" :exit-code 65535)))

(defun %fake-chain-send (c external)
  (push external (fake-sent c))
  (let ((reaction (pop (fake-script c)))
        (hash (base64-encode (map '(vector (unsigned-byte 8)) #'char-code
                                  (format nil "fake-hash-~D" (length (fake-sent c)))))))
    (when (eq reaction :end) (error "fake chain: script exhausted"))
    ;; A step that advances the seqno is the wallet consuming the external
    ;; message: record the matching transaction too, so both the seqno-based
    ;; and the hash-based confirmations see it.  :TX-OUT N sets how many
    ;; outbound messages that transaction carries (default 1).
    (dolist (step reaction)
      (let ((effects (cdr step)))
        (push (cons (+ (fake-now c) (car step))
                    (if (getf effects :seqno)
                        (list* :tx (cons hash (or (getf effects :tx-out) 1)) effects)
                        effects))
              (fake-pending c))))
    hash))

(defun apply-effects (c effects)
  (loop for (k v) on effects by #'cddr
        do (ecase k
             (:seqno (incf (fake-seqno c) v))
             (:ton (incf (fake-ton c) v))
             (:usdt (incf (fake-usdt c) v))
             ;; (:jetton (MASTER-ADDRESS . DELTA))
             (:jetton (incf (fake-jetton-balance c (car v)) (cdr v)))
             (:tx (push (make-fake-tx c (car v) (cdr v)) (fake-txs c)))
             (:tx-out nil)
             (:flow (setf (fake-flow-events c) (append (fake-flow-events c) (list v))))
             (:pools (setf (fake-pools c) v)))))

(defun %fake-chain-sleep (c seconds)
  (incf (fake-now c) seconds)
  (loop for due = (find-if (lambda (p) (<= (car p) (fake-now c))) (fake-pending c))
        while due
        do (setf (fake-pending c) (remove due (fake-pending c)))
           (apply-effects c (cdr due))))

(defun %fake-chain-wait-block (c timeout)
  (chain-sleep c timeout)
  (incf (fake-block-waits c))
  (incf (fake-head c)))

(defun test-flow-scanner-wakeups ()
  (format t "indexer: advisory scanner wakeups are drainable~%")
  (let* ((addr (fake-address #x77))
         (scanner (cl-ton::%make-flow-scanner nil (list addr)))
         (event (cl-ton::make-flow-event :pool addr :block :b
                                          :transaction :tx :observed-at 1)))
    (cl-ton::publish-flow-event scanner event)
    (check "event published" (equal (cl-ton::drain-flow-events scanner) (list event)))
    (check "drain clears" (null (cl-ton::drain-flow-events scanner))))
  (let* ((left (fake-address #x11))
         (right (fake-address #xF1))
         (zero (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))
         (left-shard (cl-ton::make-block-id :workchain 0 :shard 4611686018427387904 :seqno 1
                                           :root-hash zero :file-hash zero))
         (right-shard (cl-ton::make-block-id :workchain 0 :shard -4611686018427387904 :seqno 1
                                            :root-hash zero :file-hash zero))
         (tx (cl-ton::make-short-tx-id :account (address-hash right) :lt 1 :hash zero)))
    (check "left shard selected by address prefix"
           (and (cl-ton::shard-includes-address-p left-shard left)
                (not (cl-ton::shard-includes-address-p right-shard left))))
    (check "right shard selected by address prefix"
           (and (cl-ton::shard-includes-address-p right-shard right)
                (not (cl-ton::shard-includes-address-p left-shard right))))
    (check "short transaction account resolves to watched pool"
           (address-equal
            right
            (cl-ton::watched-pool-for-transaction (list left right) tx))))
  (let* ((trade (cl-ton::%make-tonlib (cffi:null-pointer)))
         (heads (cl-ton::%make-tonlib (cffi:null-pointer)))
         (flows (cl-ton::%make-tonlib (cffi:null-pointer)))
         (poller (cl-ton::%make-head-poller heads))
         (scanner (cl-ton::%make-flow-scanner flows nil))
         (chain (cl-ton::make-tonlib-chain trade nil nil nil nil
                                            :head-poller poller
                                            :scanner scanner)))
    (check "trading, head, and scanner clients are independently owned"
           (and (not (eq trade (cl-ton::head-poller-client poller)))
                (not (eq trade (cl-ton::flow-scanner-client scanner)))
                (not (eq (cl-ton::head-poller-client poller)
                         (cl-ton::flow-scanner-client scanner)))
                (eq trade (cl-ton::tonlib-chain-tl chain))))))

(defun run-execution-tests ()
  (let ((*log-stream* (make-broadcast-stream)))  ; keep log quiet
    (test-flow-scanner-wakeups)))
