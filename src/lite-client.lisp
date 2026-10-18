;;;; lite-client.lisp -- a verifying client of a liteserver (or of the local proxy-liteserver) over
;;;; ADNL-ext: the native counterpart of what tonlib does, in terms of the verifiers of
;;;; proof-verify.lisp and sync.lisp.
;;;;
;;;; Trust starts at ONE block id, the ANCHOR (the zero state's block, or a later block the user
;;;; trusts, e.g. the init_block of the global config).  LITE-SYNC walks proven key-block links from
;;;; the newest block it trusts to the server's head; every other answer is checked against that
;;;; block.  Nothing a server says is believed unless a verifier in this system accepted it.

(in-package :cl-ton)

(define-condition lite-error (ton-error)
  ((code :initarg :code :initform nil :reader lite-error-code))
  (:documentation "The liteserver answered with liteServer.error."))

(defstruct (lite-client (:constructor %make-lite-client) (:copier nil))
  adnl                                  ; the ADNL-EXT-CLIENT
  anchor                                ; the trusted block id the client started from
  trusted                               ; the newest masterchain block id proved so far (the head)
  key-block                             ; the newest KEY block proved: where the next sync starts from
  key-state-hash                        ; its state hash (NIL for the anchor: the zero state's is its id's)
  state-file                            ; NIL, or the file the newest key block is kept in (see below)
  (saved-seqno -1)                      ; the key block's seqno last written to STATE-FILE
  (head-slack nil)                      ; blocks a proved head may lag the liteserver's own newest (NIL: no check)
  (lookup-with-proof t)                 ; NIL once the liteserver(s) turned out not to know lookupBlockWithProof
  (proved (make-hash-table :test 'equalp)) ; pinned masterchain blocks already proved (seqno+root hash -> T)
  (libraries (make-hash-table :test 'equal)) ; library cell hash (hex) -> the proved library cell
  (config-cache nil)                    ; (seqno root-hash . config cell) of the newest block whose configuration was fetched
  (lock (sb-thread:make-mutex :name "lite client")))

(defun open-lite-client (host port server-public anchor &key name state-file head-slack)
  "A client of the liteserver at HOST:PORT (public key SERVER-PUBLIC, 32 octets) that trusts the
masterchain block ANCHOR (a tonNode.blockIdExt) and nothing else yet.  With STATE-FILE (a path)
the newest key block proved is kept there and read back by the next client with the same ANCHOR,
so a restart does not walk the whole chain again (see %LITE-LOAD-STATE for what is checked).
With HEAD-SLACK (a number of masterchain blocks) LITE-SYNC refuses a head that lags the newest block
the liteserver reports by more than that: some upstreams answer getBlockProof with a long stale head."
  (let ((client (%make-lite-client :adnl (open-adnl-ext-client host port server-public :name name)
                                   :anchor anchor :trusted anchor :key-block anchor
                                   :state-file state-file :head-slack head-slack)))
    (when state-file
      (multiple-value-bind (key state-hash) (%lite-load-state state-file anchor)
        (when key
          (setf (lite-client-trusted client) key
                (lite-client-key-block client) key
                (lite-client-key-state-hash client) state-hash
                (lite-client-saved-seqno client) (tl-get key :seqno)))))
    client))

;;; --- the persisted trust state -------------------------------------------------------
;;;
;;; What is kept is ONE masterchain key block that this client proved from its ANCHOR (its id and
;;; its state hash), like the validated state tonlib keeps in its keystore.  Whoever can write the
;;; file can move the starting point of the next run, exactly as with tonlib's keystore, so the file
;;; is private (mode 600, in a directory created 700) and is READ BACK ONLY if it is ours, not
;;; writable by others, intact (SHA-256), written for the SAME anchor and a key block that is not
;;; older than it.  Anything else is ignored and the client starts from the anchor.  The anchor
;;; itself is never taken from the file.

(defparameter +lite-state-magic+ (map '(simple-array (unsigned-byte 8) (*)) #'char-code "CLTONLS1"))

(defun %lite-state-octets (anchor key key-state-hash)
  (let ((body (concat-octets (list (tl-encode anchor) (tl-encode key)
                                   (if key-state-hash
                                       (concat-octets (list (vector 1) key-state-hash))
                                       (vector 0))))))
    (concat-octets (list +lite-state-magic+ (sha256 body) body))))

(defun %lite-same-block-p (a b)
  (and (eql (tl-get a :workchain) (tl-get b :workchain))
       (eql (tl-get a :shard) (tl-get b :shard))
       (eql (tl-get a :seqno) (tl-get b :seqno))
       (equalp (tl-get a :root-hash) (tl-get b :root-hash))
       (equalp (tl-get a :file-hash) (tl-get b :file-hash))))

(defun %lite-load-state (path anchor)
  "(VALUES key-block key-state-hash) from PATH, or NIL when the file is missing or not acceptable."
  (handler-case
      (let* ((name (namestring path))
             (st (sb-posix:stat name)))
        (unless (and (sb-posix:s-isreg (sb-posix:stat-mode st))
                     (= (sb-posix:stat-uid st) (sb-posix:geteuid))
                     (zerop (logand (sb-posix:stat-mode st) #o022))
                     (< 0 (sb-posix:stat-size st) 4096))
          (return-from %lite-load-state nil))
        (let* ((data (with-open-file (in name :element-type '(unsigned-byte 8))
                       (let ((v (make-array (file-length in) :element-type '(unsigned-byte 8))))
                         (read-sequence v in) v)))
               (head (length +lite-state-magic+)))
          (unless (and (> (length data) (+ head 32 1))
                       (equalp (subseq data 0 head) +lite-state-magic+))
            (return-from %lite-load-state nil))
          (let ((body (subseq data (+ head 32))))
            (unless (equalp (subseq data head (+ head 32)) (sha256 body))
              (return-from %lite-load-state nil))
            (multiple-value-bind (file-anchor rest) (tl-decode-prefix body)
              (multiple-value-bind (key rest) (tl-decode-prefix rest)
                (unless (and (tl-is file-anchor "tonNode.blockIdExt") (tl-is key "tonNode.blockIdExt")
                             (%lite-same-block-p file-anchor anchor)
                             (eql (tl-get key :workchain) (tl-get anchor :workchain))
                             (eql (tl-get key :shard) (tl-get anchor :shard))
                             (>= (tl-get key :seqno) (tl-get anchor :seqno)))
                  (return-from %lite-load-state nil))
                (let ((flag (aref rest 0)))
                  (cond ((and (= flag 0) (= (length rest) 1) (%lite-same-block-p key anchor))
                         (values key nil))
                        ((and (= flag 1) (= (length rest) 33) (> (tl-get key :seqno) (tl-get anchor :seqno)))
                         (values key (subseq rest 1)))
                        (t nil))))))))
    (error () nil)))

(defun lite-state-key-seqno (path)
  "The seqno of the key block a lite state file at PATH holds, or NIL when it is missing or malformed (no anchor or
checksum check here: the loader does those when the file is used).  Never signals."
  (ignore-errors
   (let* ((data (with-open-file (in (namestring path) :element-type '(unsigned-byte 8))
                  (let ((v (make-array (file-length in) :element-type '(unsigned-byte 8))))
                    (read-sequence v in) v)))
          (head (length +lite-state-magic+)))
     (when (and (< (length data) 4096) (> (length data) (+ head 32 1))
                (equalp (subseq data 0 head) +lite-state-magic+)
                (equalp (subseq data head (+ head 32)) (sha256 (subseq data (+ head 32)))))
       (multiple-value-bind (anchor rest) (tl-decode-prefix (subseq data (+ head 32)))
         (declare (ignore anchor))
         (let ((key (tl-decode-prefix rest)))
           (and (tl-is key "tonNode.blockIdExt") (tl-get key :seqno))))))))

(defun %lite-save-state (client)
  "Write the client's newest key block to its STATE-FILE (atomically); never signals."
  (let ((path (lite-client-state-file client)))
    (when path
      (multiple-value-bind (key state-hash)
          (sb-thread:with-mutex ((lite-client-lock client))
            (values (lite-client-key-block client) (lite-client-key-state-hash client)))
        (when (> (tl-get key :seqno) (lite-client-saved-seqno client))
          (handler-case
              (let* ((name (namestring path))
                     (dir (directory-namestring name))
                     (fresh (not (probe-file dir)))
                     (tmp (format nil "~A.~D.tmp" name (sb-posix:getpid))))
                (ensure-directories-exist name)
                (when fresh (sb-posix:chmod (string-right-trim "/" dir) #o700))
                (let ((fd (sb-posix:open tmp (logior sb-posix:o-wronly sb-posix:o-creat sb-posix:o-trunc) #o600)))
                  (unwind-protect
                       (let ((octets (%lite-state-octets (lite-client-anchor client) key state-hash)))
                         (sb-unix:unix-write fd octets 0 (length octets)))
                    (sb-posix:close fd)))
                (sb-posix:rename tmp name)
                (setf (lite-client-saved-seqno client) (tl-get key :seqno)))
            (error (e) (adnl-log "lite client: state not saved: ~A" e))))))))

(defun close-lite-client (client)
  (close-adnl-ext-client (lite-client-adnl client)))

(defun %lite-await-ready (client limit)
  "Wait until CLIENT's session is up or the internal real time LIMIT passes; true when it is up."
  (loop (when (adnl-ext-client-alive-p client) (return t))
        (when (or (adnl-ext-client-stop-p client) (>= (get-internal-real-time) limit)) (return nil))
        (sleep 0.05)))

(defun lite-call (client request &key (timeout 8) wait-seqno (wait-timeout 8) (retry t) (deadline (* 3 timeout)))
  "Send the TL function object REQUEST and return the decoded answer; liteServer.error signals
LITE-ERROR.  The session reconnects by itself: with RETRY true (the default) a query that finds the
session down, loses it, or gets no answer within TIMEOUT is sent again once it is back, until
DEADLINE seconds have passed in all, then the ADNL condition is signalled.  RETRY :NOT-READY retries
only a query that was never sent (what a send of a message wants), NIL never.  WAIT-SEQNO asks the
server to wait up to WAIT-TIMEOUT seconds until it has that masterchain block first (the
waitMasterchainSeqno prefix); the answer is then at least that fresh, but still unproved."
  (let* ((adnl (lite-client-adnl client))
         (start (get-internal-real-time))
         (limit (+ start (round (* deadline internal-time-units-per-second))))
         ;; how long a "not ready" (651) is asked again: long enough for a server's shard client to catch up with a
         ;; block it has just announced, short enough that a block that is not there is reported, not waited for
         (not-ready-limit (min limit (+ start (round (* 6 internal-time-units-per-second)))))
         (function (tl-encode request))
         (data (if wait-seqno
                   (concat-octets (list (tl-encode (tl-make "liteServer.waitMasterchainSeqno"
                                                            :seqno wait-seqno
                                                            :timeout-ms (round (* 1000 wait-timeout))))
                                        function))
                   function))
         (attempt-timeout (if wait-seqno (+ timeout wait-timeout) timeout))
         (payload (tl-encode (tl-make "liteServer.query" :data data))))
    (loop
      (let ((answer
              (handler-case (tl-decode (adnl-ext-client-send-query adnl payload attempt-timeout))
                (adnl-not-ready (e)
                  (unless (and retry (%lite-await-ready adnl limit)) (error e))
                  nil)
                (adnl-closed (e)
                  (unless (and (eq retry t) (%lite-await-ready adnl limit)) (error e))
                  nil)
                (adnl-timeout (e)
                  (unless (and (eq retry t) (< (get-internal-real-time) limit)) (error e))
                  nil))))
        ;; code 651 is the liteserver's "not ready": the block or state asked for is not in ITS database yet (a
        ;; masterchain block just proved, whose shard blocks the server's shard client has not stored: "block ... is
        ;; not in db (possibly out of sync: shard_client_seqno=..)").  It is the same moment every upstream is in, so
        ;; the proxy's retry elsewhere can fail too; a moment later it is there.  Asked again until the deadline.
        (when (and answer (tl-is answer "liteServer.error") (eql (tl-get answer :code) 651)
                   (eq retry t)
                   (< (+ (get-internal-real-time) (round (* 0.5 internal-time-units-per-second))) not-ready-limit))
          (sleep 0.4)
          (setf answer nil))
        (when answer
          (when (tl-is answer "liteServer.error")
            (error 'lite-error :code (tl-get answer :code)
                               :format-control "liteserver error ~D: ~A"
                               :format-arguments (list (tl-get answer :code) (tl-get answer :message))))
          (return answer))
        (when (>= (get-internal-real-time) limit)
          (error 'adnl-timeout :format-control "no answer within the ~As deadline"
                               :format-arguments (list deadline)))))))

(defun %lite-commit-key (client key key-state-hash)
  "Remember KEY, a key block just proved, as the newest one -- also as the head when it is newer than the
head -- and keep it in the state file, so a failed or interrupted sync is resumed from here and not from
the anchor.  Never moves backwards."
  (sb-thread:with-mutex ((lite-client-lock client))
    (when (> (tl-get key :seqno) (tl-get (lite-client-key-block client) :seqno))
      (setf (lite-client-key-block client) key
            (lite-client-key-state-hash client) key-state-hash)
      (when (> (tl-get key :seqno) (tl-get (lite-client-trusted client) :seqno))
        (setf (lite-client-trusted client) key))))
  (%lite-save-state client))

(define-condition lite-stale-head (ton-error) ()
  (:documentation "The proved head is older than the freshness asked for."))

(defvar *lite-proof-hook* nil
  "NIL, or a function called with every block proof the sync fetched and verified (the diagnose uses it to
capture real links as test vectors).  Its errors are ignored.")

(defun %lite-sync-rounds (client &key (max-steps 400) min-seqno (wait-timeout 8) progress trace target)
  "Prove the newest masterchain block the server has: ask getBlockProof from the newest KEY block proved
so far (MODE 2: up to the newest block of the server's liteserver state; mode 0 would end at its shard
client's state, which on some upstreams lags by hundreds of thousands of blocks; a server answers from key blocks, at most 16 links at a time -- a chain of months is dozens of
rounds) until the answer is complete (with TARGET, a block id, up to that block instead: mode 1; a server whose state
is older than the target answers an error, which the proxy retries on another upstream), verifying each with VERIFY-PARTIAL-BLOCK-PROOF.  Every key block
proved on the way is kept at once (%LITE-COMMIT-KEY), so a sync that fails or is stopped resumes where
it got to.  Returns the proved head's block id.  With MIN-SEQNO the server is asked to wait (up to
WAIT-TIMEOUT seconds) for that masterchain block before it answers, and a head older than MIN-SEQNO is
an error.  PROGRESS is called with the proved head's seqno at the end; TRACE, when given, with a line
about every round (links, key block reached, seconds fetching and verifying)."
  (multiple-value-bind (key key-state-hash)
      (sb-thread:with-mutex ((lite-client-lock client))
        (values (lite-client-key-block client) (lite-client-key-state-hash client)))
    (dotimes (i max-steps (ton-error "no complete proof of the head after ~D rounds" max-steps))
      (let* ((t0 (get-internal-real-time))
             (proof (lite-call client (if target
                                          (tl-make "liteServer.getBlockProof" :mode 1 :known-block key :target-block target)
                                          (tl-make "liteServer.getBlockProof" :mode 2 :known-block key))
                               :wait-seqno min-seqno :wait-timeout wait-timeout))
             (t1 (get-internal-real-time))
             (result (if key-state-hash
                         (verify-partial-block-proof proof key :trusted-state-hash key-state-hash)
                         (verify-partial-block-proof proof key)))
             (t2 (get-internal-real-time)))
        (when *lite-proof-hook* (ignore-errors (funcall *lite-proof-hook* proof)))
        (when (and (not (getf result :complete)) (zerop (getf result :steps)))
          (ton-error "the liteserver's block proof makes no progress"))
        (when (< (tl-get (getf result :to) :seqno) (tl-get key :seqno))
          (ton-error "the liteserver's block proof goes back from the key block ~D to ~D"
                     (tl-get key :seqno) (tl-get (getf result :to) :seqno)))
        (when (getf result :key-block)
          (setf key (getf result :key-block) key-state-hash (getf result :key-state-hash))
          (%lite-commit-key client key key-state-hash))
        (when trace
          (funcall trace (format nil "lite: round ~D: ~D link~:P, key block ~D, head ~D (fetch ~,1Fs, verify ~,1Fs)"
                                 (1+ i) (getf result :steps) (tl-get key :seqno) (tl-get (getf result :to) :seqno)
                                 (/ (- t1 t0) (float internal-time-units-per-second))
                                 (/ (- t2 t1) (float internal-time-units-per-second)))))
        (when (getf result :complete)
          (sb-thread:with-mutex ((lite-client-lock client))
            (let ((old (lite-client-trusted client)))
              (when (or (null old) (>= (tl-get (getf result :to) :seqno) (tl-get old :seqno)))
                (setf (lite-client-trusted client) (getf result :to))))
            (setf (lite-client-key-block client) key
                  (lite-client-key-state-hash client) key-state-hash))
          (%lite-save-state client)
          (when progress (funcall progress (tl-get (getf result :to) :seqno)))
          (when (and min-seqno (< (tl-get (getf result :to) :seqno) min-seqno))
            (error 'lite-stale-head :format-control "the proved head ~D is older than the ~D asked for"
                                    :format-arguments (list (tl-get (getf result :to) :seqno) min-seqno)))
          (return (getf result :to)))
        (unless (getf result :key-block)
          (ton-error "an incomplete block proof that reaches no key block"))))))

(defun lite-sync (client &rest args &key min-seqno &allow-other-keys)
  "%LITE-SYNC-ROUNDS (see there), and with the client's HEAD-SLACK set and no MIN-SEQNO given, a head at
most that many blocks behind the newest masterchain block the liteserver reports (an unproved number,
used only to refuse a stale proof: with no target a server proves up to its own shard client's state, and
an upstream that fell behind answers a complete chain to a head weeks old).  The proof is then asked for
with that seqno as the floor; a stale answer (a server whose liteserver state lags answers a complete, valid
chain to an old head) is retried, up to three tries, the second and third for the reported block itself."
  (let ((slack (lite-client-head-slack client)))
    (if (or (null slack) min-seqno)
        (apply #'%lite-sync-rounds client args)
        (let ((failure nil))
          (dotimes (attempt 3 (error failure))
            (declare (ignorable attempt))
            (handler-case
                (let* ((info (lite-call client (tl-make "liteServer.getMasterchainInfo")))
                       (floor (max 0 (- (tl-get (tl-get info :last) :seqno) slack))))
                  (return (apply #'%lite-sync-rounds client :min-seqno floor
                                 ;; the first try asks for the server's newest block, later ones for the block the
                                 ;; liteserver reported: a server not yet that far answers an error, so another one does
                                 :target (and (plusp attempt) (tl-get info :last)) args)))
              (lite-stale-head (e) (setf failure e) (sleep 1))
              (lite-error (e) (setf failure e) (sleep 1))))))))

(defun %lite-account-id (address)
  (tl-make "liteServer.accountId" :workchain (address-workchain address) :id (address-hash address)))

(defun %lite-pinned (client block)
  "BLOCK, a masterchain block id the caller pinned (the observe mode reads every pool at one block), proved to
be of the chain CLIENT trusts -- LITE-PROVE-BLOCK, once per block -- and returned."
  (let ((key (list (tl-get block :seqno) (tl-get block :root-hash))))
    (unless (sb-thread:with-mutex ((lite-client-lock client)) (gethash key (lite-client-proved client)))
      (lite-prove-block client block)
      (sb-thread:with-mutex ((lite-client-lock client))
        (when (> (hash-table-count (lite-client-proved client)) 256) (clrhash (lite-client-proved client)))
        (setf (gethash key (lite-client-proved client)) t)))
    block))

(defun lite-account-state (client address &key block)
  "The state of ADDRESS at the newest proved masterchain block -- or at BLOCK, a masterchain block id at or
below it (proved first: %LITE-PINNED) -- checked by VERIFY-ACCOUNT-STATE."
  (let* ((trusted (if block (%lite-pinned client block) (lite-sync client)))
         (answer (lite-call client (tl-make "liteServer.getAccountState" :id trusted
                                                                         :account (%lite-account-id address)))))
    (verify-account-state answer address trusted)))

(defun lite-transactions (client address &key (count 10))
  "Up to COUNT of the newest transactions of ADDRESS, newest first, chained to its proved last
transaction by VERIFY-TRANSACTION-LIST (see its result: :TRANSACTIONS :NEXT-LT :NEXT-HASH :COMPLETE)."
  (let ((state (lite-account-state client address)))
    (if (not (getf state :exists))
        (list :transactions '() :next-lt 0 :next-hash nil :complete t)
        (let ((lt (getf state :last-trans-lt)) (hash (getf state :last-trans-hash)))
          (verify-transaction-list
           (lite-call client (tl-make "liteServer.getTransactions" :count count :account (%lite-account-id address)
                                                                   :lt lt :hash hash))
           address lt hash :count count)))))

(defun lite-run-get-method (client address method stack &rest options &key block &allow-other-keys)
  "Run the getter METHOD on the proved state of ADDRESS (see RUN-ACCOUNT-GET-METHOD for STACK and
OPTIONS) -- at BLOCK, a pinned masterchain block, when given.  The values of that function: look at the exit code."
  (let ((options (loop for (k v) on options by #'cddr unless (eq k :block) append (list k v))))
    (apply #'run-account-get-method (getf (lite-account-state client address :block block) :account-cell) method stack options)))

(defun lite-server-get-method (client address method stack &key block)
  "The getter METHOD (a name or a numeric method id) of ADDRESS as the LITESERVER computes it at BLOCK, a masterchain
block id (default: the newest proved one): liteServer.runSmcMethod asked for the result only, so NOTHING of the
answer is proved.  (VALUES ITEMS EXIT-CODE) as RUN-ACCOUNT-GET-METHOD.  It is the independent check of the proved
path (the same getter run by another implementation on the state the server holds), never a source of data to act
on.  Signals LITE-ERROR (a pruned state: 602, an unknown request: -400) or when the answer is not a stack."
  (let* ((id (or block (lite-sync client)))
         (answer (lite-call client (tl-make "liteServer.runSmcMethod"
                                            :mode 4 :id id :account (%lite-account-id address)
                                            :method-id (if (integerp method) method (method-id method))
                                            :params (serialize-boc (list (serialize-vm-stack stack)) :has-crc32c nil)))))
    (unless (tl-is answer "liteServer.runMethodResult")
      (ton-error "runSmcMethod: unexpected answer ~A" (and (tl-obj-p answer) (tl-name answer))))
    (let ((result (tl-get answer :result)))
      (values (and result (plusp (length result)) (parse-vm-stack (first (parse-boc result))))
              (tl-get answer :exit-code)))))

(defun lite-send-message (client boc)
  "Hand the external message BOC (octets) to the liteserver; returns its hash, or signals if the
liteserver did not accept it.  Whether it ever lands in a block is for the caller to watch."
  (check-send-message-status (lite-call client (tl-make "liteServer.sendMessage" :body boc) :retry :not-ready))
  (external-message-hash boc))

(defun lite-shards (client)
  "The shard blocks the newest proved masterchain block refers to (see VERIFY-ALL-SHARDS-INFO): the
masterchain block id as :MC-BLOCK and the list of shard plists as :SHARDS."
  (let* ((trusted (lite-sync client))
         (answer (lite-call client (tl-make "liteServer.getAllShardsInfo" :id trusted))))
    (list :mc-block trusted :shards (getf (verify-all-shards-info answer trusted) :shards))))

(defun lite-shard-info (client workchain shard &key exact)
  "The shard block the newest proved masterchain block names for SHARD (a 64-bit shard id, signed or
not) of WORKCHAIN -- with EXACT only a block of that very shard -- checked by VERIFY-SHARD-INFO: a plist
(:FOUND :SHARD-BLOCK :SHARD :SEQNO :ROOT-HASH :FILE-HASH); :FOUND NIL when the proof shows there is none."
  (let* ((trusted (lite-sync client))
         (answer (lite-call client (tl-make "liteServer.getShardInfo"
                                            :id trusted :workchain workchain
                                            :shard (if (>= shard (expt 2 63)) (- shard (expt 2 64)) shard)
                                            :exact (and exact t)))))
    (verify-shard-info answer trusted workchain shard :exact exact)))

(defun %lite-unsupported-p (condition)
  "A liteserver that does not know the request answers error -400 (this fakechain: 400)."
  (member (lite-error-code condition) '(-400 400)))

(defun %lite-signed-shard (shard)
  (if (>= shard (expt 2 63)) (- shard (expt 2 64)) shard))

(defun %lite-bind-block (client id)
  "Place the block ID (a blockIdExt) in the chain CLIENT trusts without lookupBlockWithProof: a
masterchain block by LITE-PROVE-BLOCK (getBlockProof from the head); a shard block by getShardBlockProof
(VERIFY-SHARD-BLOCK-PROOF) and LITE-PROVE-BLOCK of the masterchain block the chain starts from.
Returns that masterchain block; signals when the block is not of the trusted chain."
  (if (= (tl-get id :workchain) -1)
      (progn (lite-prove-block client id) id)
      (let ((mc (getf (verify-shard-block-proof (lite-call client (tl-make "liteServer.getShardBlockProof" :id id)) id)
                      :mc-block)))
        (lite-prove-block client mc)
        mc)))

(defun %lite-lookup-block-plain (client workchain shard mode seqno lt utime)
  "LITE-LOOKUP-BLOCK for a liteserver without lookupBlockWithProof: the plain liteServer.lookupBlock
(VERIFY-LOOKUP-HEADER), for a lt or utime lookup the header of the block before it (VERIFY-LOOKUP-PREV-HEADER),
and the block placed in the trusted chain by %LITE-BIND-BLOCK."
  (let* ((answer (lite-call client (apply #'tl-make "liteServer.lookupBlock"
                                          :mode mode
                                          :id (tl-make "tonNode.blockId" :workchain workchain
                                                                          :shard (%lite-signed-shard shard) :seqno (or seqno 0))
                                          (append (and lt (list :lt lt)) (and utime (list :utime utime))))))
         (found (verify-lookup-header answer workchain shard mode :seqno (or seqno 0) :lt (or lt 0) :utime (or utime 0)))
         (id (getf found :block-id)))
    (when (logtest mode 6)
      (let ((p (find-if (lambda (p) (%shard-id-contains-p (getf p :shard) shard)) (getf found :prev))))
        (unless p (error 'proof-error :format-control "lookup: the proved header names no previous block of the shard"))
        (let ((prev-id (tl-block-id-ext :workchain (getf p :workchain) :shard (%lite-signed-shard (getf p :shard))
                                        :seqno (getf p :seqno) :root-hash (getf p :root-hash) :file-hash (getf p :file-hash))))
          (verify-lookup-prev-header (lite-call client (tl-make "liteServer.getBlockHeader" :id prev-id :mode 0))
                                     prev-id mode :lt (or lt 0) :utime (or utime 0)))))
    (list :block-id id :mc-block (%lite-bind-block client id) :info (getf found :info))))

(defun lite-lookup-block (client workchain shard &key seqno lt utime)
  "The block of SHARD (a 64-bit shard id) of WORKCHAIN with the given SEQNO, or the one that contains
logical time LT, or the first one generated at or after UTIME (exactly one of the three), placed in
the chain the client trusts by VERIFY-LOOKUP-BLOCK.  A plist (:BLOCK-ID :MC-BLOCK :INFO).  A liteserver
that does not know liteServer.lookupBlockWithProof (older mainnet builds answer error -400) is served
by the plain lookupBlock, getShardBlockProof and getBlockProof instead, with the same checks; the
client remembers it and does not ask that request again."
  (let* ((mode (cond ((and seqno (not lt) (not utime)) 1)
                     ((and lt (not seqno) (not utime)) 2)
                     ((and utime (not seqno) (not lt)) 4)
                     (t (ton-error "lite-lookup-block: give exactly one of :seqno, :lt, :utime"))))
         (trusted (lite-sync client)))
    (when (lite-client-lookup-with-proof client)
      (let ((answer (handler-case
                        (lite-call client
                                   (apply #'tl-make "liteServer.lookupBlockWithProof"
                                          :mode mode
                                          :id (tl-make "tonNode.blockId" :workchain workchain
                                                                          :shard (%lite-signed-shard shard) :seqno (or seqno 0))
                                          :mc-block-id trusted
                                          (append (and lt (list :lt lt)) (and utime (list :utime utime)))))
                      (lite-error (e)
                        (if (%lite-unsupported-p e) (setf (lite-client-lookup-with-proof client) nil) (error e))))))
        (when answer
          (return-from lite-lookup-block
            (verify-lookup-block answer trusted workchain shard mode :seqno (or seqno 0) :lt (or lt 0) :utime (or utime 0))))))
    (%lite-lookup-block-plain client workchain shard mode seqno lt utime)))

(defun lite-prove-block (client block-id)
  "Prove that BLOCK-ID, a masterchain block at or below the newest proved head, is a block of the
chain the client trusts: getBlockProof from the head to it (a backward link: the head's state lists it
among its previous blocks, see VERIFY-BACK-LINK), checked by VERIFY-PARTIAL-BLOCK-PROOF.  Returns its
plist (:TO ID ...); signals unless the chain is complete and ends exactly at BLOCK-ID.  Never changes
what the client trusts."
  (let ((head (lite-sync client)))
    (when (%same-block-id-p head block-id)
      (return-from lite-prove-block (list :to head :complete t :steps 0))))
  (let* ((head (lite-sync client))
         (proof (lite-call client (tl-make "liteServer.getBlockProof" :mode 1 :known-block head
                                                                      :target-block block-id)))
         (result (verify-partial-block-proof proof head)))
    (unless (and (getf result :complete) (%same-block-id-p (getf result :to) block-id))
      (error 'proof-error :format-control "the proof does not end at the block asked for"))
    result))

(defun lite-libraries (client hashes)
  "The public libraries of the masterchain among HASHES (32-octet cell hashes; the node answers the first
16), with the proof that the newest proved masterchain state publishes them, checked by
VERIFY-LIBRARIES-WITH-PROOF: a list of (HASH . CELL)."
  (let* ((trusted (lite-sync client))
         (answer (lite-call client (tl-make "liteServer.getLibrariesWithProof" :id trusted :mode 1
                                                                                :library-list (coerce hashes 'vector)))))
    (verify-libraries-with-proof answer trusted hashes :mode 1)))
