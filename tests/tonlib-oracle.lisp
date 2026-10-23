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

;;;; tonlib-oracle.lisp -- the JSON tonlib (libtonlibjson through CFFI), a TEST ORACLE.
;;;;
;;;; The bot reads the chain through the verifying lite client; this file keeps the old tonlibjson backend for the tests
;;;; (A/B against the lite client, the fakechain flows).  It ships with the test build only, and registers its entry points
;;;; in *TONLIB-ORACLE* and the methods of TONLIB-JSON-OP (tonlib.lisp).
;;;;
;;;; tonlibjson is asynchronous: SEND enqueues a request, RECEIVE returns  
;;;; the next response or update. TONLIB-CALL correlates them with the  
;;;; "@extra" field through one dedicated sb-thread receive pump per client.  
;;;; Callers retain a synchronous interface while parallel calls wait  
;;;; independently. Unsolicited updates (updateSyncState etc.) are dropped.

(in-package :cl-ton)

(cffi:define-foreign-library tonlibjson
  (:unix (:or "tonlibjson-linux-x86_64.so"))
  (t (:default "tonlibjson")))

(cffi:defcfun ("tonlib_client_json_create" %tl-create) :pointer)

(cffi:defcfun ("tonlib_client_json_destroy" %tl-destroy) :void (client :pointer))

(cffi:defcfun ("tonlib_client_json_send" %tl-send) :void (client :pointer) (request :string))

(cffi:defcfun ("tonlib_client_json_receive" %tl-receive) :string (client :pointer) (timeout :double))

(cffi:defcfun ("tonlib_client_set_verbosity_level" %tl-set-verbosity) :void (level :int))

(defvar *tonlib-loaded* nil)

(defun load-tonlib-library (&optional path)
  (unless *tonlib-loaded*
    (if path
        (cffi:load-foreign-library path)
        (cffi:use-foreign-library tonlibjson))
    (setf *tonlib-loaded* t)))

(defstruct (tonlib-waiter (:constructor make-tonlib-waiter ()))
  (lock (sb-thread:make-mutex :name "tonlib waiter") :read-only t)
  (queue (sb-thread:make-waitqueue :name "tonlib waiter") :read-only t)
  response
  failure
  done-p)

(defstruct (tonlib (:constructor %make-tonlib (handle)))
  (handle (cffi:null-pointer) :type cffi:foreign-pointer)
  (lock (sb-thread:make-mutex :name "tonlib send") :read-only t)
  (waiters-lock (sb-thread:make-mutex :name "tonlib waiters") :read-only t)
  (waiters (make-hash-table :test #'equal) :read-only t)
  (pump-ready-lock (sb-thread:make-mutex :name "tonlib pump ready") :read-only t)
  (pump-ready-queue (sb-thread:make-waitqueue :name "tonlib pump ready") :read-only t)
  pump-ready-p
  pump-failure
  pump-thread
  stop-p
  closing-p
  (counter 0 :type fixnum)
  (timeout 30.0d0 :type double-float))

(defun tonlib-alive-p (tl)
  (when (lite-client-p tl) (return-from tonlib-alive-p (adnl-ext-client-alive-p (lite-client-adnl tl))))
  (and (not (tonlib-closing-p tl))
       (not (cffi:null-pointer-p (tonlib-handle tl)))))

(defun json-encode (plist)
  (let ((json-compile (jonathan:compile-encoder (:from :plist) (plist) `,plist)))
    (funcall json-compile plist)))

(defun finish-tonlib-waiter (waiter &key response failure)
  (sb-thread:with-mutex ((tonlib-waiter-lock waiter))
    (unless (tonlib-waiter-done-p waiter)
      (setf (tonlib-waiter-response waiter) response
            (tonlib-waiter-failure waiter) failure
            (tonlib-waiter-done-p waiter) t)
      (sb-thread:condition-notify (tonlib-waiter-queue waiter)))))

(defun dispatch-tonlib-response (tl raw)
  (let* ((obj (json-decode raw))
         (id (json-get obj "@extra"))
         (waiter (and id
                      (sb-thread:with-mutex ((tonlib-waiters-lock tl))
                        (prog1 (gethash id (tonlib-waiters tl))
                          (remhash id (tonlib-waiters tl)))))))
    (when waiter
      (finish-tonlib-waiter waiter :response obj))))

(defun tonlib-receive-pump-step (tl)
  "Drain all responses currently available from TL. This is the only live
client path that calls %TL-RECEIVE."
  (handler-case
      (loop for raw = (%tl-receive (tonlib-handle tl) 0.0d0)
            while raw
            do (dispatch-tonlib-response tl raw))
    (error (e)
      (warn "tonlib receive pump: ~A" e))))

(defun start-tonlib-pump (tl)  
  "Start TL's receive pump on a dedicated thread and wait until it is running."  
  (setf (tonlib-pump-thread tl)  
        (sb-thread:make-thread  
         (lambda ()  
           (handler-case  
               (progn  
                 (sb-thread:with-mutex ((tonlib-pump-ready-lock tl))  
                   (setf (tonlib-pump-ready-p tl) t)  
                   (sb-thread:condition-notify (tonlib-pump-ready-queue tl)))  
                 (loop until (tonlib-stop-p tl)  
                       do (tonlib-receive-pump-step tl)  
                          (sleep 0.001)))  
             (error (e)  
               (sb-thread:with-mutex ((tonlib-pump-ready-lock tl))  
                 (setf (tonlib-pump-failure tl) e)  
                 (sb-thread:condition-notify (tonlib-pump-ready-queue tl))))))  
         :name "tonlib receive pump"))  
  (sb-thread:with-mutex ((tonlib-pump-ready-lock tl))  
    (loop until (or (tonlib-pump-ready-p tl) (tonlib-pump-failure tl))  
          do (sb-thread:condition-wait (tonlib-pump-ready-queue tl)  
                                       (tonlib-pump-ready-lock tl)))  
    (when (tonlib-pump-failure tl)
      (error (tonlib-pump-failure tl))))
  tl)

(defun create-tonlib-client ()
  (let ((tl (%make-tonlib (%tl-create))))
    (handler-case
        (start-tonlib-pump tl)
      (error (e)
        (%tl-destroy (tonlib-handle tl))
        (setf (tonlib-handle tl) (cffi:null-pointer))
        (error e)))))

(defun fail-tonlib-waiters (tl message)
  (let ((waiters
          (sb-thread:with-mutex ((tonlib-waiters-lock tl))
            (prog1 (loop for waiter being the hash-values of (tonlib-waiters tl)
                         collect waiter)
              (clrhash (tonlib-waiters tl))))))
    (dolist (waiter waiters)
      (finish-tonlib-waiter waiter :failure message))))

(defun wait-for-tonlib-waiter (waiter deadline)
  (block wait
    (sb-thread:with-mutex ((tonlib-waiter-lock waiter))
      (loop
        (when (tonlib-waiter-done-p waiter)
          (return-from wait t))
        (let ((remaining (/ (- deadline (get-internal-real-time))
                            internal-time-units-per-second)))
          (when (<= remaining 0)
            (return-from wait nil))
          (unless
              (sb-thread:condition-wait
               (tonlib-waiter-queue waiter)
               (tonlib-waiter-lock waiter)
               :timeout remaining)
            (return-from wait nil)))))))

(defun tonlib-call (tl request &key (timeout (tonlib-timeout tl)))
  "Send REQUEST, a TYPED tonlib_api function object (TLAPI-MAKE), and return its @extra-correlated Jonathan
hash table.  Every request that reaches tonlibjson goes through here, so every one is validated against the
schema before it is sent (tonlib's JSON layer would otherwise silently ignore a misspelt field).
The old one-second receive timeout was polling cadence, not a latency floor."
  (unless (tlapi-obj-p request)
    (ton-error "tonlib-call takes a typed tonlib_api object (TLAPI-MAKE), not ~S" request))
  (unless (tonlib-alive-p tl) (ton-error "tonlib client is closed"))
  (let* ((id (sb-thread:with-mutex ((tonlib-lock tl))
               (format nil "req-~D" (incf (tonlib-counter tl)))))
         (waiter (make-tonlib-waiter))
         (deadline (+ (get-internal-real-time)
                      (* timeout internal-time-units-per-second))))
    (sb-thread:with-mutex ((tonlib-waiters-lock tl))
      (unless (tonlib-alive-p tl) (ton-error "tonlib client is closed"))
      (setf (gethash id (tonlib-waiters tl)) waiter))
    (handler-case
        (sb-thread:with-mutex ((tonlib-lock tl))
          ;; CLOSE-TONLIB destroys the native client under this same lock, so re-checking
          ;; here is what keeps a sender that passed the unlocked check above (another
          ;; thread closing between the two) from calling into a destroyed client, which
          ;; aborts the whole process (tonlib's ActorOwn "!empty()" check).
          (unless (and (tonlib-alive-p tl) (not (tonlib-closing-p tl)))
            (ton-error "tonlib client is closed"))
          (%tl-send (tonlib-handle tl)
                    (json-encode (append (tlapi->plist request) (list :|@extra| id)))))
      (error (e)
        (sb-thread:with-mutex ((tonlib-waiters-lock tl))
          (remhash id (tonlib-waiters tl)))
        (error e)))
    (unless (wait-for-tonlib-waiter waiter deadline)
      (sb-thread:with-mutex ((tonlib-waiters-lock tl))
        (when (eq waiter (gethash id (tonlib-waiters tl)))
          (remhash id (tonlib-waiters tl))))
      (ton-error "tonlib request ~A timed out after ~As" id timeout))
    (sb-thread:with-mutex ((tonlib-waiter-lock waiter))
      (when (tonlib-waiter-failure waiter)
        (ton-error "~A" (tonlib-waiter-failure waiter)))
      (let ((obj (tonlib-waiter-response waiter)))
        (when (equal (json-get obj "@type") "error")
          (error 'tonlib-error :code (json-get obj "code")
                               :message (json-get obj "message")))
        obj))))

;;; --- global config loading -----------------------------------------------
;;;
;;; Liteserver reachability used to be handled here by probing every address
;;; in the public global config and ranking survivors (TCP-connect race).
;;; That path is gone: EFFECTIVE-GLOBAL-CONFIG (bot.lisp) now always routes
;;; through the cl-ton liteserver-proxy layer (proxy-liteserver.lisp), which
;;; gives tonlib a single already-live entry instead of a list to rank.
;;; CONFIG-WITH-LITESERVERS survives because the proxy path still uses it to
;;; splice its one entry into a copy of the raw config.

(defun initialize-tonlib-client (config keystore sync sync-timeout sync-attempts &optional sync-progress)
  (let ((tl (create-tonlib-client)))
    (handler-case
        (progn
          (tonlib-call
           tl
           (tlapi-make "init"
                       :options (tlapi-make "options"
                                            :config (tlapi-make "config" :config config
                                                                         :use-callbacks-for-network nil
                                                                         :blockchain-name "" :ignore-cache nil)
                                            :keystore-type (if (eq keystore :in-memory)
                                                               (tlapi-make "keyStoreTypeInMemory")
                                                               (tlapi-make "keyStoreTypeDirectory"
                                                                           :directory keystore)))))
          (when sync
            (tonlib-sync tl :attempts sync-attempts :timeout sync-timeout :progress sync-progress))
          tl)
      (error (e)
        (close-tonlib tl)
        (error e)))))

(defun open-tonlib (config-path &key library-path (verbosity 0) (keystore :in-memory) (sync t) sync-progress)
  "Create and initialise a tonlib client from a global config file (normally
the single-entry config the liteserver-proxy writes; see
EFFECTIVE-GLOBAL-CONFIG in bot.lisp). With SYNC (default) the client is
synchronised to the latest masterchain block before returning, so later
queries are fast and not racing the liteserver handshake.  SYNC-PROGRESS, a function returning
a count that grows as verified work is done (the proxy's answered block-proof queries), makes
that sync patient: see TONLIB-SYNC."
  (load-tonlib-library library-path)
  (%tl-set-verbosity verbosity)
  (initialize-tonlib-client (read-global-config config-path) keystore sync 120.0d0 8 sync-progress))

(defparameter *tonlib-sync-retry-delay* 2
  "Seconds between the attempts of a patient TONLIB-SYNC.")

(defun %retryable-tonlib-error-p (e)
  (typecase e
    (tonlib-error (or (eql (tonlib-error-code e) 500)
                      (search "LITE_SERVER" (tonlib-error-message e))))
    (ton-error (search "timed out" (princ-to-string e)))))

(defun tonlib-sync (tl &key (attempts 8) (timeout 120.0d0) progress (total-timeout 1800) (max-stalled 3)
                         on-attempt)
  "Block until tonlib has the latest masterchain block; returns its seqno.
Liteservers frequently time out during the first sync, so this retries.

The first sync of a fresh keystore walks a chain of block proofs from the config's init block, one
verified step after another; over a weak link that takes minutes, and a failed attempt does not
undo the steps already verified.  With PROGRESS (a function returning a number that grows with
every verified step) the sync is therefore PATIENT: it keeps retrying as long as an attempt added
progress, and gives up only after MAX-STALLED attempts in a row added none, after TOTAL-TIMEOUT
seconds, or on an error that retrying cannot help.  ON-ATTEMPT is called after each failed
attempt with (attempt-number error steps-gained progress-now).  Without PROGRESS it is simply
ATTEMPTS tries, as before."
  (when (lite-client-p tl) (return-from tonlib-sync (tl-get (lite-sync tl) :seqno)))
  (if (null progress)
      (retrying (lambda ()
                  (json-get (tonlib-call tl (tlapi-make "sync") :timeout timeout) "seqno"))
                :attempts attempts :delay 2.0)
      (let ((deadline (+ (get-universal-time) total-timeout))
            (last (funcall progress))
            (stalled 0))
        (loop for attempt from 1
              do (handler-case
                     (return (json-get (tonlib-call tl (tlapi-make "sync") :timeout timeout) "seqno"))
                   ((or tonlib-error ton-error) (e)
                     (let* ((now (funcall progress)) (gained (- now last)))
                       (setf last now)
                       (if (plusp gained) (setf stalled 0) (incf stalled))
                       (when on-attempt (funcall on-attempt attempt e gained now))
                       (warn-atomically "tonlib sync: ~A (attempt ~D, ~D verified step~:P gained, ~D in total)"
                                        e attempt gained now)
                       (when (or (not (%retryable-tonlib-error-p e))
                                 (>= stalled max-stalled)
                                 (> (get-universal-time) deadline))
                         (error e))
                       (sleep *tonlib-sync-retry-delay*))))))))

(defmacro with-tonlib ((var config-path &rest options) &body body)
  `(let ((,var (open-tonlib ,config-path ,@options)))
     (unwind-protect (progn ,@body)
       (close-tonlib ,var))))

(defun %account-address-obj (addr)
  (tlapi-make "accountAddress" :account-address (address->string addr)))

(defun %block-obj (block)
  "A masterchain/shard block id as a typed ton.blockIdExt (BLOCK is one already, or a decoded JSON document)."
  (cond ((tlapi-obj-p block) block)
        ((hash-table-p block) (json->tlapi block))
        (t (ton-error "not a block id: ~S" block))))

(defun %cell-octets (cell) (coerce (base64-decode (cell->base64 cell)) 'tl-octets))

(defun %stack-entry (item)
  "A TVM stack value as a typed tvm.StackEntry (what STACK-ITEM->JSON builds as a plist)."
  (cond ((eq item :null) (ton-error "tonlib cannot pass null stack entries"))
        ((integerp item)
         (tlapi-make "tvm.stackEntryNumber"
                     :number (tlapi-make "tvm.numberDecimal" :number (format nil "~D" item))))
        ((cell-p item)
         (tlapi-make "tvm.stackEntryCell" :cell (tlapi-make "tvm.cell" :bytes (%cell-octets item))))
        ((slice-p item)
         (unless (and (zerop (slice-bit-pos item)) (zerop (slice-ref-pos item)))
           (ton-error "tonlib slices must start at the cell beginning"))
         (tlapi-make "tvm.stackEntrySlice" :slice (tlapi-make "tvm.slice" :bytes (%cell-octets (slice-cell item)))))
        (t (ton-error "Cannot encode stack item ~S for tonlib" item))))

(defun %typed-get-transactions (block mode count after)
  "The typed blocks.getTransactions for the arguments COLLECT-BLOCK-TRANSACTIONS (the lean pager shared with the lite
backend) passes its requester."
  (tlapi-make "blocks.getTransactions"
              :id (%block-obj block)
              :mode mode
              :count count
              :after (or after
                         ;; the first page: the zero account id, lt 0
                         (tlapi-make "blocks.accountTransactionId"
                                     :account (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)
                                     :lt 0))))

;;; --- the entry points the lean code reaches through *TONLIB-ORACLE* ---------------------------------------------------

(defun close-tonlib-ffi (tl)
  "Close a JSON tonlib client (CLOSE-TONLIB's non-lite branch)."
  (when (tonlib-alive-p tl)
    (setf (tonlib-closing-p tl) t)
    (fail-tonlib-waiters tl "tonlib client closed")
    (setf (tonlib-stop-p tl) t)
    (when (tonlib-pump-thread tl)
      (sb-thread:join-thread (tonlib-pump-thread tl) :default nil :timeout 5))
    (if (and (tonlib-pump-thread tl)
             (sb-thread:thread-alive-p (tonlib-pump-thread tl)))
        (warn "tonlib receive pump did not stop; retaining native handle")
        (progn
          ;; take the send lock: no TONLIB-CALL may be inside %TL-SEND while the client dies,
          ;; and any later one sees the null handle / closing flag and signals instead
          (sb-thread:with-mutex ((tonlib-lock tl))
            (%tl-destroy (tonlib-handle tl))
            (setf (tonlib-handle tl) (cffi:null-pointer))))))
  nil)

(defun open-tonlib-via-proxy (proxy global-config-path &key library-path (verbosity 0)
                                                           (keystore :in-memory) (sync t) output-path)
  "Route a JSON tonlib client through PROXY (either implementation): write GLOBAL-CONFIG-PATH's JSON with its
liteservers replaced by PROXY's single 127.0.0.1 entry (PROXY-LITESERVER-GLOBAL-CONFIG-PATH), then OPEN-TONLIB on that.
Returns (VALUES TONLIB ROUTED-CONFIG-PATH).  The routed config is checked to name exactly one liteserver, on loopback,
before tonlib ever sees it: a tonlib that could reach anything else would defeat the point of the proxy (and of tests
that must touch no real network)."
  (let* ((out (or output-path
                  (merge-pathnames "tonlib-via-proxy.global.json"
                                   (uiop:ensure-directory-pathname (proxy-liteserver-db proxy)))))
         (path (proxy-liteserver-global-config-path proxy global-config-path out)))
    (check-routed-config path)
    (values (open-tonlib path :library-path library-path :verbosity verbosity
                              :keystore keystore :sync sync
                              :sync-progress (proxy-progress-function proxy))
            path)))

(setf *tonlib-oracle* (list :load #'load-tonlib-library :open #'open-tonlib :close #'close-tonlib-ffi
                            :sync #'tonlib-sync :open-via-proxy #'open-tonlib-via-proxy :call #'tonlib-call))

;;; --- the operations of TONLIB-JSON-OP ----------------------------------------------------------------------------------


(defmethod tonlib-json-op ((tl tonlib) (op (eql :masterchain-block)) &key timeout)
  (json->tlapi (json-get (tonlib-call tl (tlapi-make "blocks.getMasterchainInfo")
                                      :timeout (or timeout (tonlib-timeout tl)))
                         "last")))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :shards)) &key block timeout)
  (mapcar #'json->tlapi
          (json-get (retrying
                     (lambda ()
                       (tonlib-call tl (tlapi-make "blocks.getShards" :id (%block-obj block))
                                    :timeout (or timeout (tonlib-timeout tl)))))
                    "shards")))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :block-transactions)) &key block count timeout)
  (collect-block-transactions
   (lambda (block mode count after)
     (let ((response (retrying (lambda ()
                                 (tonlib-call tl (%typed-get-transactions block mode count after)
                                              :timeout (or timeout (tonlib-timeout tl)))))))
       (values (mapcar #'json->tlapi (json-get response "transactions"))
               (json-get response "incomplete"))))
   block count))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :account-state)) &key addr)
  (let* ((r (retrying (lambda ()
                        (tonlib-call tl (tlapi-make "raw.getAccountState" :account-address (%account-address-obj addr))))))
         (code (json-get r "code"))
         (data (json-get r "data"))
         (frozen (json-get r "frozen_hash")))
    (make-account-state
     :address addr
     :balance (max 0 (parse-integer (json-get r "balance"))) ; -1 for accounts never seen
     :code (and code (plusp (length code)) (base64->cell code))
     :data (and data (plusp (length data)) (base64->cell data))
     :last-lt (parse-integer (json-get r "last_transaction_id" "lt"))
     :last-hash (json-get r "last_transaction_id" "hash")
     :status (cond ((and code (plusp (length code))) :active)
                   ((and frozen (plusp (length frozen))) :frozen)
                   (t :uninit))
     :sync-utime (json-get r "sync_utime"))))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :run-get-method)) &key addr method stack)
  "smc.load + smc.runGetMethod + smc.forget; smc.load is pinned to *GET-METHOD-BLOCK* via withBlock when it is set."
  (retrying
   (lambda ()
     (let* ((load-req (tlapi-make "smc.load" :account-address (%account-address-obj addr)))
            (loaded (tonlib-call tl (if *get-method-block*
                                        (tlapi-make "withBlock" :id (%block-obj *get-method-block*) :function load-req)
                                        load-req)))
            (id (json-get loaded "id")))
       (unwind-protect
            (let ((r (tonlib-call tl (tlapi-make "smc.runGetMethod"
                                                 :id id
                                                 :method (tlapi-make "smc.methodIdName" :name method)
                                                 :stack (mapcar #'%stack-entry stack)))))
              (values (mapcar #'json->stack-item (json-get r "stack"))
                      (json-get r "exit_code")))
         (ignore-errors (tonlib-call tl (tlapi-make "smc.forget" :id id))))))))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :send-message)) &key message-cell)
  (json-get (tonlib-call tl (tlapi-make "raw.sendMessageReturnHash" :body (%cell-octets message-cell)))
            "hash"))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :config-cell)) &key)
  (base64->cell (json-get (retrying (lambda ()
                                      (tonlib-call tl (tlapi-make "getConfigAll" :mode 0))))
                          "config" "bytes")))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :shard-account-cell)) &key addr)
  (base64->cell (json-get (retrying (lambda ()
                                      (tonlib-call tl (tlapi-make "getShardAccountCell"
                                                            :account-address (%account-address-obj addr)))))
                          "bytes")))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :libraries)) &key hashes)
  (let ((r (retrying (lambda ()
                       (tonlib-call tl (tlapi-make "smc.getLibraries"
                                             :library-list (mapcar (lambda (h) (coerce h 'tl-octets)) hashes)))))))
    (mapcar (lambda (entry)
              (cons (octets->hex (base64-decode (json-get entry "hash")))
                    (base64->cell (json-get entry "data"))))
            (json-get r "result"))))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :transactions)) &key addr from-lt from-hash)
  (let* ((st (if (and from-lt from-hash) nil (tonlib-account-state tl addr)))
         (lt (or from-lt (account-state-last-lt st)))
         (hash (or from-hash (base64-decode (account-state-last-hash st)))))
    (if (zerop lt)
        '()
        (mapcar #'json->tlapi
                (json-get (retrying (lambda ()
                              (tonlib-call tl (tlapi-make "raw.getTransactions"
                                                          :private-key (tlapi-make "inputKeyFake")
                                                          :account-address (%account-address-obj addr)
                                                          :from-transaction-id
                                                          (tlapi-make "internal.transactionId"
                                                                      :lt lt
                                                                      :hash (coerce hash 'tl-octets))))))
                  "transactions")))))

;;; --- tonlibjson's JSON stack entries (a test-side format; the application feeds libemulator a stack cell) ------------------

(defun stack-item->json (item)
  (cond ((eq item :null)
         (ton-error "tonlib cannot pass null stack entries"))
        ((integerp item)
         (list :|@type| "tvm.stackEntryNumber"
               :|number| (list :|@type| "tvm.numberDecimal" :|number| (format nil "~D" item))))
        ((cell-p item)
         (list :|@type| "tvm.stackEntryCell"
               :|cell| (list :|@type| "tvm.cell" :|bytes| (cell->base64 item))))
        ((slice-p item)
         (unless (and (zerop (slice-bit-pos item)) (zerop (slice-ref-pos item)))
           (ton-error "tonlib slices must start at the cell beginning"))
         (list :|@type| "tvm.stackEntrySlice"
               :|slice| (list :|@type| "tvm.slice" :|bytes| (cell->base64 (slice-cell item)))))
        (t (ton-error "Cannot encode stack item ~S for tonlib" item))))

(defun json->stack-item (entry)
  (let ((type (json-get entry "@type")))
    (cond ((equal type "tvm.stackEntryNumber")
           (parse-integer (json-get entry "number" "number")))
          ((equal type "tvm.stackEntryCell")
           (base64->cell (json-get entry "cell" "bytes")))
          ((equal type "tvm.stackEntrySlice")
           (cell-slice (base64->cell (json-get entry "slice" "bytes"))))
          ((member type '("tvm.stackEntryTuple" "tvm.stackEntryList") :test #'equal)
           (cons :tuple (mapcar #'json->stack-item
                                (json-get entry (if (equal type "tvm.stackEntryTuple") "tuple" "list")
                                          "elements"))))
          (t (ton-error "Unsupported tonlib stack entry ~S" type)))))

;;; --- the JSON bridge of the typed tonlib API (tonlib's tl_json conventions) ------------------------------------------------------------

(defun %tlapi->json (type value)
  (ecase (if (consp type) (first type) type)
    ((:int32 :int53 :flags) value)
    (:int64 (format nil "~D" value))
    ((:int256 :bytes :secure-bytes) (base64-encode value))
    ((:string :secure-string) value)
    (:bool (if value t :false))
    (:double value)
    (:vector (map 'list (lambda (e) (%tlapi->json (second type) e)) (coerce value 'vector)))
    ((:bare :class :object :function) (tlapi->plist value))))

(defun tlapi->plist (obj)
  "OBJ as the plist tonlibjson takes: (:|@type| NAME :|field_name| VALUE ...), fields in schema
order, nested objects as nested plists, int64 as a decimal string, bytes as base64, Bool as
T / :FALSE (what Jonathan turns into true / false)."
  (let ((con (tlapi-find (tlapi-obj-name obj))) (fields (tlapi-obj-fields obj)))
    (list* :|@type| (tlapi-obj-name obj)
           (loop for (fname . type) in (tlapi-con-fields con)
                 for key = (tl-field-key fname)
                 when (tl-plist-has-key-p fields key)
                   append (list (intern fname :keyword)
                                (%tlapi->json (if (eq (and (consp type) (first type)) :if) (fourth type) type)
                                              (getf fields key)))))))

(defun %json->tlapi (type json path)
  (flet ((need (ok what) (unless ok (%tlapi-bad path "expected ~A in JSON, got ~S" what json))))
    (ecase (if (consp type) (first type) type)
      ((:int32 :int53 :flags) (need (integerp json) "a number") json)
      (:int64 (cond ((integerp json) json)
                    ((stringp json) (or (ignore-errors (parse-integer json))
                                        (%tlapi-bad path "bad int64 string ~S" json)))
                    (t (need nil "an int64"))))
      ((:int256 :bytes :secure-bytes)
       (need (stringp json) "a base64 string")
       (let ((octets (coerce (base64-decode json) 'tl-octets)))
         (when (and (eq type :int256) (/= (length octets) 32))
           (%tlapi-bad path "int256 of ~D octets" (length octets)))
         octets))
      ((:string :secure-string) (need (stringp json) "a string") json)
      (:bool (and json (not (eq json :false)) t))
      (:double (need (realp json) "a number") (float json 1d0))
      (:vector (need (listp json) "an array")
       (loop for e in json for i from 0
             collect (%json->tlapi (second type) e (format nil "~A[~D]" path i))))
      ((:bare :class :object :function)
       (need (hash-table-p json) "an object")
       (let ((obj (%json->obj json path)))
         (case (if (consp type) (first type) type)
           (:bare (unless (string= (tlapi-obj-name obj) (second type))
                    (%tlapi-bad path "expected a ~A, got a ~A" (second type) (tlapi-obj-name obj))))
           (:class (unless (string= (tlapi-con-class (tlapi-find (tlapi-obj-name obj))) (second type))
                     (%tlapi-bad path "expected a ~A, got a ~A" (second type) (tlapi-obj-name obj)))))
         obj)))))

(defun %json->obj (json path)
  (let* ((name (gethash "@type" json))
         (con (progn (unless (stringp name) (%tlapi-bad path "JSON object without @type"))
                     (tlapi-find name)))
         (path (if (equal path "") name path)))
    (%make-tlapi-obj
     name
     (loop for (fname . type) in (tlapi-con-fields con)
           for json-value = (multiple-value-list (gethash fname json))
           when (second json-value)
             append (list (tl-field-key fname)
                          (%json->tlapi (if (eq (and (consp type) (first type)) :if) (fourth type) type)
                                        (first json-value) (format nil "~A.~A" path fname)))))))

(defun json->tlapi (json)
  "A decoded tonlibjson answer (a Jonathan hash table with \"@type\") -> a typed object.  Lenient
about what tonlib may add or omit (unknown JSON fields are dropped, absent ones stay absent -- use
TLAPI-VALIDATE to demand a complete object); strict about types and constructor classes."
  (%json->obj json ""))
