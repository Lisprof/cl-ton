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

;;;; indexer.lisp -- advisory confirmed-flow scanner for watched pools.
;;;;
;;;; This path only observes block-visible transactions. It never authorizes a
;;;; trade or supplies balances; trading always re-reads through CHAIN.

(in-package :cl-ton)

(defvar *flow-event-hook* nil)

(defstruct (flow-event (:copier nil))
  pool
  block
  transaction
  observed-at)

(defstruct (flow-scanner (:constructor %make-flow-scanner (client watched)))
  client
  watched
  (lock (sb-thread:make-mutex :name "confirmed-flow scanner") :read-only t)
  (queue (sb-thread:make-waitqueue :name "confirmed-flow scanner") :read-only t)
  events
  callback
  last-seqno
  stop-p
  thread)

(defun uint64 (value)
  (ldb (byte 64 0) value))

(defun shard-includes-address-p (shard addr)
  (let* ((workchain (json-get shard "workchain"))
         (raw-shard (json-get shard "shard"))
         (shard-id (uint64 (if (stringp raw-shard)
                               (parse-integer raw-shard)
                               raw-shard)))
         (tag (logand shard-id (- shard-id)))
         (mask (uint64 (- (* 2 tag))))
         (prefix (octets->uint (address-hash addr) :end 8)))
    (and (= workchain (address-workchain addr))
         (= (logand prefix mask) (logand shard-id mask)))))

(defun tx-account-hash (tx)
  (let ((account (or (json-get tx "account")
                     (json-get tx "account_addr")
                     (json-get tx "address"))))
    (cond ((typep account 'address) (address-hash account))
          ((stringp account)
           (or (let ((decoded (ignore-errors (base64-decode account))))
                 (and decoded (= (length decoded) 32) decoded))
               (let ((addr (ignore-errors (parse-address account))))
                 (and addr (address-hash addr)))))
          (t nil))))

(defun watched-pool-for-transaction (watched tx)
  (let ((hash (tx-account-hash tx)))
    (and hash
         (find hash watched :test #'equalp :key #'address-hash))))

(defparameter *flow-event-backlog* 1000
  "Most undrained events a scanner keeps.  Events are advisory; a consumer that
never drains (or drains rarely, as a cycle tracker does) must not make the
list grow for the life of the process, so the OLDEST are dropped first.")

(defun publish-flow-event (scanner event)
  (sb-thread:with-mutex ((flow-scanner-lock scanner))
    (push event (flow-scanner-events scanner))
    ;; newest first, so trimming the tail drops the oldest
    (let ((tail (nthcdr (1- *flow-event-backlog*) (flow-scanner-events scanner))))
      (when tail (setf (cdr tail) nil)))
    (sb-thread:condition-broadcast (flow-scanner-queue scanner))))

(defun drain-flow-events (scanner)
  (when scanner
    (sb-thread:with-mutex ((flow-scanner-lock scanner))
      (prog1 (nreverse (flow-scanner-events scanner))
      (setf (flow-scanner-events scanner) nil)))))

(defun scanner-stopped-p (scanner)
  (sb-thread:with-mutex ((flow-scanner-lock scanner))
    (flow-scanner-stop-p scanner)))

(defun scan-confirmed-flow-once (scanner)
  (let* ((client (flow-scanner-client scanner))
         (master (tonlib-masterchain-block client :timeout 5.0d0))
         (seqno (json-get master "seqno")))
    (unless (eql seqno (flow-scanner-last-seqno scanner))
      (let ((shards (tonlib-shards client master :timeout 5.0d0)))
        (dolist (shard shards)
          (when (some (lambda (addr) (shard-includes-address-p shard addr))
                      (flow-scanner-watched scanner))
            (dolist (tx (tonlib-block-transactions client shard
                                                   :count nil
                                                   :timeout 5.0d0))
              (let ((pool
                      (watched-pool-for-transaction
                       (flow-scanner-watched scanner) tx)))
                (when pool
                  (let ((event
                          (make-flow-event :pool pool
                                           :block shard
                                           :transaction tx
                                           :observed-at (unix-now))))
                    (publish-flow-event scanner event)
                    (when (flow-scanner-callback scanner)
                      (funcall (flow-scanner-callback scanner) event))))))))
        (setf (flow-scanner-last-seqno scanner) seqno)))))

(defun start-flow-scanner (client watched-pools &key (interval 1) callback)
  "Start advisory scanner on CLIENT. Failures are logged and non-fatal."
  (let ((scanner (%make-flow-scanner client watched-pools)))
    (setf (flow-scanner-callback scanner) callback)
    (setf (flow-scanner-thread scanner)
          (sb-thread:make-thread
           (lambda ()
             (loop until (scanner-stopped-p scanner)
                   do (handler-case
                          (scan-confirmed-flow-once scanner)
                        (error (e)
                          (warn "confirmed-flow scanner: ~A" e)))
                      (sleep interval)))
           :name "TON confirmed-flow scanner"))
    scanner))

(defun stop-flow-scanner (scanner)
  (when scanner
    (sb-thread:with-mutex ((flow-scanner-lock scanner))
      (setf (flow-scanner-stop-p scanner) t)
      (sb-thread:condition-broadcast (flow-scanner-queue scanner)))
    (when (flow-scanner-thread scanner)
      (sb-thread:join-thread (flow-scanner-thread scanner)
                             :default nil :timeout 5))
    ;; Never close the client under a scanner thread that is still running.
    (if (and (flow-scanner-thread scanner)
             (sb-thread:thread-alive-p (flow-scanner-thread scanner)))
        (warn "flow scanner thread did not stop in 5s; leaving its tonlib client open")
        (close-tonlib (flow-scanner-client scanner))))
  nil)
