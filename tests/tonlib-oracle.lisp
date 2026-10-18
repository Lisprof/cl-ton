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
  "Send REQUEST and return its @extra-correlated Jonathan hash table.
The old one-second receive timeout was polling cadence, not a latency floor."
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
                    (json-encode (append request (list :|@extra| id)))))
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
           (list :|@type| "init"
                 :|options| (list :|@type| "options"
                                  :|config| (list :|@type| "config"
                                                  :|config| config
                                                  :|use_callbacks_for_network| :false
                                                  :|blockchain_name| ""
                                                  :|ignore_cache| :false)
                                  :|keystore_type| (if (eq keystore :in-memory)
                                                       (list :|@type| "keyStoreTypeInMemory")
                                                       (list :|@type| "keyStoreTypeDirectory"
                                                             :|directory| keystore)))))
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
                  (json-get (tonlib-call tl (list :|@type| "sync") :timeout timeout) "seqno"))
                :attempts attempts :delay 2.0)
      (let ((deadline (+ (get-universal-time) total-timeout))
            (last (funcall progress))
            (stalled 0))
        (loop for attempt from 1
              do (handler-case
                     (return (json-get (tonlib-call tl (list :|@type| "sync") :timeout timeout) "seqno"))
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

(defun account-address-json (addr)
  (list :|@type| "accountAddress" :|account_address| (address->string addr)))

(defun collect-block-transactions (requester block count)
  (loop with after = nil
        with left = count
        with transactions = nil
        while (or (null left) (plusp left))
        for page-size = (if left (min left 256) 256)
        for request = (append
                       (list :|@type| "blocks.getTransactions"
                             :|id| block
                             :|mode| (if after 135 7)
                             :|count| page-size)
                       (when after (list :|after| after)))
        for response = (funcall requester request)
        for page = (json-get response "transactions")
        do (setf transactions (nconc transactions (copy-list page)))
           (when left (decf left (length page)))
           (unless (and (json-get response "incomplete")
                        page
                        (or (null left) (plusp left)))
             (return transactions))
           (let ((last (car (last page))))
             (setf after
                   (list :|@type| "blocks.accountTransactionId"
                         :|account| (json-get last "account")
                         :|lt| (json-get last "lt"))))
        finally (return transactions)))

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
  (json-get (tonlib-call tl (list :|@type| "blocks.getMasterchainInfo")
                         :timeout (or timeout (tonlib-timeout tl)))
            "last"))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :shards)) &key block timeout)
  (json-get (retrying
             (lambda ()
               (tonlib-call tl (list :|@type| "blocks.getShards" :|id| block)
                            :timeout (or timeout (tonlib-timeout tl)))))
            "shards"))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :block-transactions)) &key block count timeout)
  (collect-block-transactions
   (lambda (request)
     (retrying (lambda () (tonlib-call tl request :timeout (or timeout (tonlib-timeout tl))))))
   block count))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :account-state)) &key addr)
  (let* ((r (retrying (lambda ()
                        (tonlib-call tl (list :|@type| "raw.getAccountState"
                                              :|account_address| (account-address-json addr))))))
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
     (let* ((load-req (list :|@type| "smc.load" :|account_address| (account-address-json addr)))
            (loaded (tonlib-call tl (if *get-method-block*
                                        (list :|@type| "withBlock" :|id| *get-method-block* :|function| load-req)
                                        load-req)))
            (id (json-get loaded "id")))
       (unwind-protect
            (let ((r (tonlib-call tl (list :|@type| "smc.runGetMethod"
                                           :|id| id
                                           :|method| (list :|@type| "smc.methodIdName" :|name| method)
                                           :|stack| (mapcar #'stack-item->json stack)))))
              (values (mapcar #'json->stack-item (json-get r "stack"))
                      (json-get r "exit_code")))
         (ignore-errors (tonlib-call tl (list :|@type| "smc.forget" :|id| id))))))))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :send-message)) &key message-cell)
  (json-get (tonlib-call tl (list :|@type| "raw.sendMessageReturnHash"
                                  :|body| (cell->base64 message-cell)))
            "hash"))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :config-cell)) &key)
  (base64->cell (json-get (retrying (lambda ()
                                      (tonlib-call tl (list :|@type| "getConfigAll" :|mode| 0))))
                          "config" "bytes")))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :shard-account-cell)) &key addr)
  (base64->cell (json-get (retrying (lambda ()
                                      (tonlib-call tl (list :|@type| "getShardAccountCell"
                                                            :|account_address| (account-address-json addr)))))
                          "bytes")))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :libraries)) &key hashes)
  (let ((r (retrying (lambda ()
                       (tonlib-call tl (list :|@type| "smc.getLibraries"
                                             :|library_list| (mapcar #'base64-encode hashes)))))))
    (mapcar (lambda (entry)
              (cons (octets->hex (base64-decode (json-get entry "hash")))
                    (base64->cell (json-get entry "data"))))
            (json-get r "result"))))

(defmethod tonlib-json-op ((tl tonlib) (op (eql :transactions)) &key addr from-lt from-hash)
  (let* ((st (if (and from-lt from-hash) nil (tonlib-account-state tl addr)))
         (lt (or from-lt (account-state-last-lt st)))
         (hash (or from-hash (account-state-last-hash st))))
    (if (zerop lt)
        '()
        (json-get (retrying (lambda ()
                              (tonlib-call tl (list :|@type| "raw.getTransactions"
                                                    :|account_address| (account-address-json addr)
                                                    :|from_transaction_id|
                                                    (list :|@type| "internal.transactionId"
                                                          :|lt| (format nil "~D" lt)
                                                          :|hash| hash)))))
                  "transactions"))))
