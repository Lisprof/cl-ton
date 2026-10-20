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

;;;; tonlib.lisp -- the chain-client surface (TONLIB-ACCOUNT-STATE, TONLIB-RUN-GET-METHOD, ...) served by the verifying
;;;; lite client (lite-backend.lisp), plus the helpers every backend shares (keystores, retries, getters).
;;;;
;;;; The JSON tonlib (libtonlibjson through CFFI) is a TEST ORACLE and lives in tests/tonlib-oracle.lisp: it ships with
;;;; the test build only.  A client that is not a LITE-CLIENT is handed to TONLIB-JSON-OP, which the oracle implements;
;;;; without the oracle it signals an error that says so.

(in-package :cl-ton)

(defun json-decode (string) (jonathan:parse string :as :hash-table))

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

;; The paging of blocks.getTransactions-shaped answers: REQUESTER takes one request (a plist) and returns one page
;; (a JSON document with "transactions" and "incomplete"); used by the lite backend and by the test-only JSON tonlib.
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

;;; --- the JSON tonlib oracle seam ---------------------------------------------------------------------------

(defvar *tonlib-oracle* '()
  "Plist of the JSON tonlib's entry points (:LOAD :OPEN :CLOSE :SYNC :OPEN-VIA-PROXY :CALL), set when tests/tonlib-oracle.lisp
is loaded (the test build); empty in the lean build, which reads the chain through the lite client only.")

(defun tonlib-oracle (key)
  "The JSON tonlib entry point KEY, or an error when the oracle is not loaded."
  (or (getf *tonlib-oracle* key)
      (ton-error "the JSON tonlib (~(~A~)) is a test oracle and is not part of this build: use the :lite chain backend" key)))

(defgeneric tonlib-json-op (tl op &key &allow-other-keys)
  (:documentation "One operation (OP, a keyword, with keyword arguments) of the JSON tonlib client TL.  The methods are
in tests/tonlib-oracle.lisp; without them this default signals the error above.")
  (:method (tl op &key &allow-other-keys)
    (declare (ignore tl))
    (tonlib-oracle op)))

(defun close-tonlib (tl)
  "Close a chain client: the lite client here, the JSON tonlib through the oracle."
  (if (lite-client-p tl)
      (close-lite-client tl)
      (funcall (tonlib-oracle :close) tl)))

(defvar *get-method-block* nil
  "When bound to a ton.blockIdExt, getters read that specific masterchain block instead of the client's newest
proved head.  NIL means read the client's current head (unpinned).  Conveyed to PMAP workers.")
(pushnew '*get-method-block* *pmap-conveyed*)

(defun tonlib-masterchain-block (tl &key timeout)
  "Return the internal.blockIdExt for the last known masterchain block."
  (if (lite-client-p tl)
      (lite-backend-masterchain-block tl)
      (tonlib-json-op tl :masterchain-block :timeout timeout)))

(defun tonlib-masterchain-info (tl &key timeout)
  "Returns the masterchain seqno of the last known block."
  (json-get (tonlib-masterchain-block tl :timeout timeout) "seqno"))

(defun tonlib-shards (tl block &key timeout)
  "The shard block ids of a masterchain internal.blockIdExt."
  (if (lite-client-p tl)
      (lite-backend-shards tl block)
      (tonlib-json-op tl :shards :block block :timeout timeout)))

(defun tonlib-block-transactions (tl block &key (count 40) timeout)
  "Return up to COUNT short transaction ids from a shard block.
COUNT may be NIL to follow pagination until the block is complete."
  (if (lite-client-p tl)
      (lite-backend-block-transactions tl block :count count)
      (tonlib-json-op tl :block-transactions :block block :count count :timeout timeout)))

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
  "The account's balance, code, data and last transaction, as an ACCOUNT-STATE."
  (if (lite-client-p tl)
      (lite-backend-account-state tl addr)
      (tonlib-json-op tl :account-state :addr addr)))

(defun tonlib-run-get-method (tl addr method &optional stack)
  "Run getter METHOD of ADDR.  Returns (values ITEMS EXIT-CODE).  When *GET-METHOD-BLOCK* is set the state is read at
that block."
  (if (lite-client-p tl)
      (lite-backend-run-get-method tl addr method stack)
      (tonlib-json-op tl :run-get-method :addr addr :method method :stack stack)))

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
  "Broadcast an external message; returns the message hash as base64."
  (if (lite-client-p tl)
      (lite-backend-send-message tl message-cell)
      (tonlib-json-op tl :send-message :message-cell message-cell)))

(defun tonlib-config-cell (tl)
  "Full config dictionary cell (getConfigAll), as required by the emulator."
  (if (lite-client-p tl)
      (lite-backend-config-cell tl)
      (tonlib-json-op tl :config-cell)))

(defun tonlib-shard-account-cell (tl addr)
  "ShardAccount cell for ADDR, the emulator's account input."
  (if (lite-client-p tl)
      (lite-backend-shard-account-cell tl addr)
      (tonlib-json-op tl :shard-account-cell :addr addr)))

(defun tonlib-libraries (tl hashes)
  "Alist of (hash-hex . cell) for the given 32-byte library hashes."
  (if (lite-client-p tl)
      (lite-backend-libraries tl hashes)
      (tonlib-json-op tl :libraries :hashes hashes)))

(defun tonlib-transactions (tl addr &key (from-lt nil) (from-hash nil))
  "The account's transactions from the given tx id (defaults to the latest): the raw list of raw.transaction hash
tables."
  (if (lite-client-p tl)
      (lite-backend-transactions tl addr :from-lt from-lt :from-hash from-hash)
      (tonlib-json-op tl :transactions :addr addr :from-lt from-lt :from-hash from-hash)))

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
