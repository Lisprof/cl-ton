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

;;;; tonlib.lisp -- CFFI binding to libtonlibjson plus typed wrappers.
;;;;
;;;; tonlibjson is asynchronous: SEND enqueues a request, RECEIVE returns  
;;;; the next response or update. TONLIB-CALL correlates them with the  
;;;; "@extra" field through one dedicated sb-thread receive pump per client.  
;;;; Callers retain a synchronous interface while parallel calls wait  
;;;; independently. Unsolicited updates (updateSyncState etc.) are dropped.

(in-package :cl-ton)

(cffi:define-foreign-library tonlibjson
  (:unix (:or "../lib/tonlibjson-linux-x86_64.so"))
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
  (and (not (tonlib-closing-p tl))
       (not (cffi:null-pointer-p (tonlib-handle tl)))))

(defun json-encode (plist)
  (let ((json-compile (jonathan:compile-encoder (:from :plist) (plist) `,plist)))
    (funcall json-compile plist)))
(defun json-decode (string) (jonathan:parse string :as :hash-table))

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

(defun config-with-liteservers (config servers)
  (let ((out (make-hash-table :test #'equal)))
    (maphash (lambda (k v) (setf (gethash k out) v)) config)
    (setf (gethash "liteservers" out) servers)
    out))

(defun read-global-config (path)
  "Global config JSON text, verbatim."
  (with-open-file (in path :external-format :utf-8)
    (let ((s (make-string (file-length in))))
      (subseq s 0 (read-sequence s in)))))

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

(defun ensure-keystore (dir)
  "tonlib needs an existing directory; returns its namestring (or :in-memory).  The directory is
made private to the owner (mode 700): it holds tonlib's validated sync state, which tonlib trusts
when it reads it back."
  (if (or (null dir) (eq dir :in-memory))
      :in-memory
      (let ((path (ensure-directories-exist (uiop:ensure-directory-pathname dir))))
        (ignore-errors (sb-posix:chmod (string-right-trim "/" (namestring path)) #o700))
        (namestring path))))

(defun derived-keystore (dir name)
  "The keystore directory of the tonlib client called NAME, kept under the main keystore DIR
(each client needs a directory of its own).  :IN-MEMORY when DIR is."
  (if (or (null dir) (eq dir :in-memory))
      :in-memory
      (ensure-keystore (merge-pathnames (format nil "~A/" name) (uiop:ensure-directory-pathname dir)))))

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

(defun close-tonlib (tl)  
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

(defmacro with-tonlib ((var config-path &rest options) &body body)
  `(let ((,var (open-tonlib ,config-path ,@options)))
     (unwind-protect (progn ,@body)
       (close-tonlib ,var))))

;; Several threads (parallel pool resolution) retry at once; unserialized WARNs interleave
;; character by character on stderr and make the log unreadable.
(defvar *warn-lock* (sb-thread:make-mutex :name "tonlib warn"))

(defun warn-atomically (control &rest args)
  (sb-thread:with-mutex (*warn-lock*)
    (warn "~A" (apply #'format nil control args))))

(defun retrying (thunk &key (attempts 6) (delay 2.0))
  "Retry THUNK on liteserver-side tonlib errors (timeouts, unavailable)."
  (flet ((retry-or-fail (e attempt retryable)
           (if (and retryable (< attempt attempts))
               (progn (warn-atomically "tonlib: ~A (attempt ~D/~D)" e attempt attempts) (sleep delay))
               (error e))))
    (loop for attempt from 1
          do (handler-case (return (funcall thunk))
               (tonlib-error (e)
                 (retry-or-fail e attempt (or (eql (tonlib-error-code e) 500)
                                              (search "LITE_SERVER" (tonlib-error-message e)))))
               (ton-error (e)
                 (retry-or-fail e attempt (search "timed out" (princ-to-string e))))))))

;;; --- resolve-time getter retry --------------------------------------------
;;;
;;; RETRYING (above) already retries inside one tonlib request.  Pool
;;; resolution needs one more layer: it used to turn EVERY getter failure into
;;; "nothing is deployed there", so a network blip at startup silently
;;; disabled a DEX's cycle.  A getter failure is now sorted into two kinds:
;;;
;;;   definitive -- the contract (or account) itself answered "no": a nonzero
;;;                 exit code, or an account that is not active.  Not retried.
;;;   anything else (tonlib/liteserver errors, timeouts, closed client, ...) --
;;;                 retried, and if it persists it is re-signalled as what it
;;;                 is, never reported as absence.

(defparameter *getter-retry-attempts* 3
  "Tries CALL-WITH-GETTER-RETRY makes before giving up on a transient failure.")

(defparameter *getter-retry-delay* 2
  "Seconds between those tries (doubled each time).")

(defun definitive-getter-failure-p (condition)
  "True when CONDITION is the contract/account answering that it cannot serve
the call (exit code, not active) rather than a transport-level failure."
  (and (typep condition 'ton-error)
       (not (typep condition 'tonlib-error))
       (let ((text (princ-to-string condition)))
         (or (search "exit code" text)      ; "... failed [locally] with exit code N"
             (search "not active" text)))   ; "<addr> is not active"
       t))

(defun call-with-getter-retry (thunk &key (attempts *getter-retry-attempts*)
                                          (delay *getter-retry-delay*))
  "Call THUNK; on a non-definitive TON-ERROR wait and retry up to ATTEMPTS
times in total, then re-signal the last error.  Definitive failures
(DEFINITIVE-GETTER-FAILURE-P) are re-signalled at once."
  (loop for attempt from 1
        do (handler-case (return (funcall thunk))
             (ton-error (e)
               (when (or (definitive-getter-failure-p e) (>= attempt attempts))
                 (error e))
               (warn-atomically "getter: ~A (attempt ~D/~D); retrying" e attempt attempts)
               (sleep (* delay (expt 2 (1- attempt))))))))

;;; --- typed wrappers ---------------------------------------------------

(defun account-address-json (addr)
  (list :|@type| "accountAddress" :|account_address| (address->string addr)))

(defun tonlib-masterchain-block (tl &key (timeout (tonlib-timeout tl)))
  "Return the internal.blockIdExt for the last known masterchain block."
  (json-get (tonlib-call tl (list :|@type| "blocks.getMasterchainInfo")
                             :timeout timeout)
            "last"))

(defun tonlib-masterchain-info (tl &key (timeout (tonlib-timeout tl)))
  "Returns the masterchain seqno of the last known block."
  (json-get (tonlib-masterchain-block tl :timeout timeout) "seqno"))

(defun tonlib-shards (tl block &key (timeout (tonlib-timeout tl)))
  "blocks.getShards for a masterchain internal.blockIdExt."
  (json-get (retrying
             (lambda ()
               (tonlib-call tl (list :|@type| "blocks.getShards"
                                     :|id| block)
                            :timeout timeout)))
            "shards"))

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

(defun tonlib-block-transactions (tl block &key (count 40)
                                             (timeout (tonlib-timeout tl)))
  "Return up to COUNT short transaction ids from a shard block.
COUNT may be NIL to follow pagination until the block is complete."
  (collect-block-transactions
   (lambda (request)
     (retrying (lambda () (tonlib-call tl request :timeout timeout))))
   block count))

(defstruct (account-state (:copier nil))
  (address nil :read-only t)
  (balance 0 :type integer :read-only t)          ; nanoTON
  (code nil :read-only t)                         ; cell or nil
  (data nil :read-only t)                         ; cell or nil
  (last-lt 0 :type integer :read-only t)
  (last-hash "" :read-only t)                     ; base64
  (status :uninit :read-only t)                   ; :active :uninit :frozen
  (sync-utime 0 :read-only t))

(defun tonlib-account-state (tl addr)
  "raw.getAccountState -> ACCOUNT-STATE (balance, code, data, last tx)."
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

(defvar *get-method-block* nil  
  "When bound to a ton.blockIdExt, smc.load runs inside a withBlock envelope so  
get-methods read that specific masterchain head instead of the client's last  
sync point.  NIL means read the client's current head (unpinned).")  
  
(defun tonlib-run-get-method (tl addr method &optional stack)  
  "smc.load + smc.runGetMethod + smc.forget.  Returns (values ITEMS EXIT-CODE).  
When *GET-METHOD-BLOCK* is set, smc.load is pinned to that block via withBlock."  
  (retrying  
   (lambda ()  
     (let* ((load-req (list :|@type| "smc.load"  
                            :|account_address| (account-address-json addr)))  
            (loaded (tonlib-call tl (if *get-method-block*  
                                        (list :|@type| "withBlock"  
                                              :|id| *get-method-block*  
                                              :|function| load-req)  
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

;; (defun tonlib-run-get-method (tl addr method &optional stack)
;;   "smc.load + smc.runGetMethod + smc.forget.  Returns (values ITEMS EXIT-CODE)."
;;   (retrying
;;    (lambda ()
;;      (let* ((loaded (tonlib-call tl (list :|@type| "smc.load"
;;                                           :|account_address| (account-address-json addr))))
;;             (id (json-get loaded "id")))
;;        (unwind-protect
;;             (let ((r (tonlib-call tl (list :|@type| "smc.runGetMethod"
;;                                            :|id| id
;;                                            :|method| (list :|@type| "smc.methodIdName" :|name| method)
;;                                            :|stack| (mapcar #'stack-item->json stack)))))
;;               (values (mapcar #'json->stack-item (json-get r "stack"))
;;                       (json-get r "exit_code")))
;;          (ignore-errors (tonlib-call tl (list :|@type| "smc.forget" :|id| id))))))))

(defun make-tonlib-getter (tl)
  (lambda (addr method stack)
    (multiple-value-bind (items exit-code) (tonlib-run-get-method tl addr method stack)
      (unless (member exit-code '(0 1))
        (ton-error "~A on ~A failed with exit code ~A" method (address->string addr) exit-code))
      items)))

(defun library-cell-hash (cell)
  "Hex hash referenced by a library cell (exotic, tag 2), else NIL."
  (and (cell-exotic-p cell)
       (= (cell-bit-length cell) 264)
       (= (ldb (byte 8 256) (cell-bits cell)) 2)
       (octets->hex (uint->octets (ldb (byte 256 0) (cell-bits cell)) 32))))

(defun collect-library-hashes (&rest cells)
  "Hex hashes of every library-reference cell (exotic, tag 2) reachable from CELLS, each once.
Contracts that keep their pool / LP / vault code in on-chain libraries (STON.fi v2) reference
it this way; the emulator needs those libraries (see TONLIB-LIBRARIES, FAKECHAIN-ADD-LIBRARY)."
  (let ((seen (make-hash-table :test #'equal)) (found '()))
    (labels ((walk (cell)
               (let ((key (cell-hash-hex cell)))
                 (unless (gethash key seen)
                   (setf (gethash key seen) t)
                   (let ((lib (library-cell-hash cell)))
                     (when lib (pushnew lib found :test #'string-equal)))
                   (dolist (ref (coerce (cell-refs cell) 'list)) (walk ref))))))
      (dolist (c cells) (when c (walk c))))
    (nreverse found)))

(defun make-local-getter (tl config-cell)
  "Getter that fetches code/data via tonlib and runs the method in libemulator.
Contracts whose code is a library cell (STON.fi pools) get the library
fetched once through smc.getLibraries and cached."
  (let ((libraries (make-hash-table :test #'equal))
        (lock (sb-thread:make-mutex :name "library cache")))
    (flet ((library (hex)
             (sb-thread:with-mutex (lock)
               (or (gethash hex libraries)
                   (setf (gethash hex libraries)
                         (or (cdr (assoc hex (tonlib-libraries tl (list (hex->octets hex)))
                                         :test #'string-equal))
                             (ton-error "library ~A not found" hex)))))))
      (lambda (addr method stack)
        (let* ((st (tonlib-account-state tl addr))
               (lib-hash (and (account-state-code st) (library-cell-hash (account-state-code st)))))
          (unless (eq (account-state-status st) :active)
            (ton-error "~A is not active" (address->string addr)))
          (multiple-value-bind (items exit-code) (run-get-method-local
                                                  (account-state-code st) (account-state-data st)
                                                  method stack
                                                  :address addr :balance (account-state-balance st)
                                                  :config config-cell
                                                  :libraries (and lib-hash
                                                                  (list (cons lib-hash (library lib-hash)))))
            (unless (member exit-code '(0 1))
              (ton-error "~A on ~A failed locally with exit code ~A" method (address->string addr) exit-code))
            items))))))

(defun tonlib-send-message (tl message-cell)
  "raw.sendMessageReturnHash; returns the message hash as base64."
  (json-get (tonlib-call tl (list :|@type| "raw.sendMessageReturnHash"
                                  :|body| (cell->base64 message-cell)))
            "hash"))

(defun tonlib-config-cell (tl)
  "Full config dictionary cell (getConfigAll), as required by the emulator."
  (base64->cell (json-get (retrying (lambda ()
                                      (tonlib-call tl (list :|@type| "getConfigAll" :|mode| 0))))
                          "config" "bytes")))

(defun tonlib-shard-account-cell (tl addr)
  "ShardAccount cell for ADDR (getShardAccountCell), the emulator's account input."
  (base64->cell (json-get (retrying (lambda ()
                                      (tonlib-call tl (list :|@type| "getShardAccountCell"
                                                            :|account_address| (account-address-json addr)))))
                          "bytes")))

(defun tonlib-libraries (tl hashes)
  "smc.getLibraries -> alist of (hash-hex . cell) for the given 32-byte hashes."
  (let ((r (retrying (lambda ()
                       (tonlib-call tl (list :|@type| "smc.getLibraries"
                                             :|library_list| (mapcar #'base64-encode hashes)))))))
    (mapcar (lambda (entry)
              (cons (octets->hex (base64-decode (json-get entry "hash")))
                    (base64->cell (json-get entry "data"))))
            (json-get r "result"))))

(defun tonlib-transactions (tl addr &key (from-lt nil) (from-hash nil))
  "raw.getTransactions from the given tx id (defaults to the latest).
Returns the raw list of raw.transaction hash tables."
  (let* ((st (if (and from-lt from-hash)
                 nil
                 (tonlib-account-state tl addr)))
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

;;; --- reading raw.transaction documents -------------------------------------
;;;
;;; TONLIB-TRANSACTIONS returns Jonathan hash tables shaped like tonlib's
;;; raw.transaction: utime, transaction_id {lt hash}, in_msg (raw.message:
;;; source destination value hash body_hash ...), out_msgs [raw.message].

(defun transaction-out-count (tx)
  (length (json-get tx "out_msgs")))

(defun transaction-matches-broadcast-p (tx &key message-hash normalized-hash body-hash)
  "True when TX (a raw.transaction) is the one that consumed a broadcast
external message.  Each identity is optional; any one matching is enough:
MESSAGE-HASH is the base64 string CHAIN-SEND returned, NORMALIZED-HASH and
BODY-HASH are octet vectors computed locally (EXTERNAL-MESSAGE-NORMALIZED-
HASH / the signed body cell's own hash).  BODY-HASH is compared against
the consumed message's body_hash, which cannot be perturbed by how the
message envelope was serialised; it is unique because the body carries the
wallet's seqno and signature."
  (let ((in-hash (json-get tx "in_msg" "hash"))
        (in-body-hash (json-get tx "in_msg" "body_hash")))
    (flet ((same-b64 (candidate actual)
             (and candidate (stringp actual)
                  (or (string= candidate actual)
                      (let ((a (ignore-errors (base64-decode actual)))
                            (c (ignore-errors (base64-decode candidate))))
                        (and a c (equalp a c))))))
           (same-octets (octets actual)
             (and octets (stringp actual)
                  (let ((a (ignore-errors (base64-decode actual))))
                    (and a (equalp a (as-octets octets)))))))
      (or (same-b64 message-hash in-hash)
          (same-octets normalized-hash in-hash)
          (same-octets body-hash in-body-hash)))))

