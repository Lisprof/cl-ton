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

;;;; proxy-liteserver.lisp -- the project's proxy-liteserver: a NATIVE Lisp
;;;; reimplementation of utils/proxy-liteserver.cpp (TON monorepo), plus the
;;;; original supervision of the released binary, kept behind a flag.
;;;;
;;;; What proxy-liteserver is (per its own --help): "Proxy liteserver:
;;;; distributes incoming queries to servers in global config."  Given a
;;;; normal global config it holds real ADNL-ext sessions to every liteserver
;;;; listed in it and exposes ONE stable local liteserver endpoint that routes
;;;; queries through those sessions -- no block validation, no state storage.
;;;;
;;;; Two implementations sit behind OPEN-PROXY-LITESERVER's unchanged
;;;; signature (plus an :IMPLEMENTATION key):
;;;;
;;;;   :NATIVE (default)  this file: Phase C clients (adnl-ext-client.lisp)
;;;;                      dial the upstreams, Phase D (adnl-ext-server.lisp)
;;;;                      listens on 127.0.0.1, and PROXY-HANDLE-QUERY does the
;;;;                      select-server / seqno-watermark / failover / failure-path
;;;;                      work.  Beyond the C++ proxy it (1) polls every
;;;;                      upstream's masterchain seqno (START-PROXY-POLLER) and avoids
;;;;                      stale ones (*PROXY-MAX-LAG*), (2) retries a query on another
;;;;                      upstream when one answers "not ready / not in db" (error 651,
;;;;                      a lagging shard client) and avoids it for
;;;;                      *PROXY-LAGGING-PENALTY* seconds, and (3) lets the first
;;;;                      queries wait *PROXY-STARTUP-GRACE* seconds for an upstream to
;;;;                      come alive.  These only change WHICH upstream answers; the
;;;;                      wire behaviour (error codes and texts) matches the binary.
;;;;   :BINARY            the released `proxy-liteserver` executable, launched
;;;;                      and supervised as before.  Kept so the same scenarios
;;;;                      can be run through it for A/B verification -- where
;;;;                      the binary and the C++ source diverge, the binary is
;;;;                      the ground truth and the native code matches it.
;;;;
;;;; The pure config-rewriting half (PROXY-LITESERVER-ENTRY, -CONFIG,
;;;; -GLOBAL-CONFIG-PATH, IPV4-STRING->IP-INT) is implementation-independent and
;;;; unchanged: tonlib is handed a single 127.0.0.1 entry either way, and
;;;; OPEN-TONLIB needs no changes at all.
;;;;
;;;; Identity files match the binary's, so a database is interchangeable:
;;;;   <db>/config.json           {"@type":"proxyLiteserver.config","port":N,"id":{pub.ed25519 key}}
;;;;   <db>/keyring/<HEX short id>  pk.ed25519 (4B constructor id + 32B seed)

(in-package :cl-ton)

(defstruct proxy-liteserver
  "A supervised PROXY-LITESERVER process. PROCESS is the UIOP process-info
handle for the running binary. PORT and the ADNL id it's serving under are
read back from its own <db>/config.json (see READ-PROXY-LITESERVER-IDENTITY)
rather than trusted from whatever :PORT OPEN-PROXY-LITESERVER was called
with, since :PORT is only honored on a database's first launch."
  process
  binary
  db
  global-config
  port
  native)                               ; a LISP-PROXY when :implementation :native

(defparameter *proxy-query-timeout* 8
  "Seconds a forwarded query may take before the proxy synthesizes a
liteServer.error instead of leaving the client hanging.")

(defstruct (lisp-proxy (:constructor %make-lisp-proxy) (:copier nil))
  keypair server upstreams db
  (lock (sb-thread:make-mutex :name "lisp-proxy"))
  (global-max-seqno 0)
  (query-timeout *proxy-query-timeout*)
  (wait-policy :plan)
  (stop-p nil)                          ; set by CLOSE-NATIVE-PROXY: the pollers exit
  (ever-alive-p nil)                    ; an upstream has been alive at least once (see PROXY-AWAIT-UPSTREAM)
  pollers                               ; one freshness-poller thread per upstream
  log-fn                                ; (control &rest args) or NIL: diagnostic lines (see OPEN-NATIVE-PROXY)
  (max-active 8)                        ; upstream sessions kept open at once, the rest stand by (see PROXY-SUPERVISE)
  supervisor                            ; the thread that keeps MAX-ACTIVE sessions open
  (method-latency (make-hash-table :test 'equal)) ; METHOD -> (n . ewma-seconds) of answered attempts
  (served (make-hash-table :test 'equal)) ; METHOD -> (n total-seconds max-seconds slow) as tonlib saw it
                                         ; (retries included); SLOW counts answers later than 8 s
  (stats (make-hash-table :test #'equal)))

(defstruct (proxy-upstream (:copier nil))
  name client
  (seqno 0)                             ; last masterchain seqno seen in one of its answers
  (penalty-until 0)                     ; internal-real-time until which it is avoided (it answered "not ready")
  slices                                ; NIL = full server; else parsed slice descriptions
  (polls 0)                             ; freshness polls attempted
  (polls-ok 0)                          ; ... that returned a masterchainInfo
  (poll-state nil)                      ; NIL (none yet) / :OK / :ERROR -- the LATEST poll
  poll-detail                           ; text of the latest failure, or the seqno of the latest success
  (poll-at nil)                         ; universal time of the latest poll
  (outcomes (make-hash-table :test 'equal))    ; (METHOD OUTCOME DETAIL) -> count, see PROXY-RECORD-OUTCOME
  (latency (make-hash-table :test 'equal))     ; METHOD -> (n total-seconds max-seconds) of ANSWERED attempts
  (slowness nil)                        ; EWMA of answer time relative to the method's usual time (1.0 = typical)
  (fail-streak 0)                       ; consecutive timeouts / lost connections; reset by an answer
  host port public                      ; where to connect (kept so a standby session can be started later)
  (started-p t))                        ; NIL while on standby: its session has not been opened yet

(defun proxy-liteserver-config-file (proxy)
  "The config.json PROXY's own process writes into its db on first launch
and reads back on every launch after -- see OPEN-PROXY-LITESERVER."
  (merge-pathnames "config.json" (uiop:ensure-directory-pathname (proxy-liteserver-db proxy))))

(defun read-proxy-liteserver-identity (proxy)
  "(VALUES PORT ID-BASE64) read back from PROXY's own config.json. Pure
once that file exists; signals TON-ERROR if PROXY hasn't written one yet
(OPEN-PROXY-LITESERVER waits for exactly this before returning, so this
only fires if the file was later removed or PROXY was never actually
opened through OPEN-PROXY-LITESERVER)."
  (let ((path (proxy-liteserver-config-file proxy)))
    (unless (probe-file path)
      (ton-error "proxy-liteserver hasn't written ~A yet -- not started, or still on its first launch" path))
    (let ((parsed (json-decode (uiop:read-file-string path))))
      (values (json-get parsed "port")
              (json-get (json-get parsed "id") "key")))))

(defun ipv4-string->ip-int (dotted)
  "The signed 32-bit big-endian integer a TON global config uses for an
IPv4 address -- the exact inverse of IP->OCTET-VECTOR (tonlib.lisp), which
decodes this same encoding for every liteserver already in a normal
global.config.json."
  (let* ((parts (uiop:split-string dotted :separator "."))
         (octets (map 'vector (lambda (s) (parse-integer s)) parts))
         (unsigned (octets->uint octets)))
    (if (>= unsigned (expt 2 31)) (- unsigned (expt 2 32)) unsigned)))

(defun proxy-liteserver-entry (proxy)
  "The single-element liteservers list that routes every query through
PROXY instead of a public server directly -- same shape as any entry
already in an ordinary global config, just always pointed at localhost."
  (multiple-value-bind (port id) (read-proxy-liteserver-identity proxy)
    (let ((entry (make-hash-table :test #'equal))
          (id-hash (make-hash-table :test #'equal)))
      (setf (gethash "@type" id-hash) "pub.ed25519"
            (gethash "key" id-hash) id)
      (setf (gethash "ip" entry) (ipv4-string->ip-int "127.0.0.1")
            (gethash "port" entry) port
            (gethash "id" entry) id-hash)
      (list entry))))

(defun proxy-liteserver-config (proxy config)
  "CONFIG (parsed the way READ-GLOBAL-CONFIG returns it) with its
liteservers replaced by PROXY's own single local entry. Everything
downstream -- OPEN-TONLIB, the existing probe/rank pipeline -- is
unchanged; it now always finds exactly one liteserver, always on
localhost, already holding real sessions to the servers CONFIG itself
named."
  (config-with-liteservers config (proxy-liteserver-entry proxy)))

(defun proxy-liteserver-global-config-path (proxy global-config-path output-path)
  "Side effect: write GLOBAL-CONFIG-PATH's own JSON, with its liteservers
replaced by PROXY's single local entry (see PROXY-LITESERVER-CONFIG), out
to OUTPUT-PATH, and return OUTPUT-PATH.

OPEN-TONLIB (tonlib.lisp) only ever takes a config *path*, not a parsed
structure -- READ-GLOBAL-CONFIG opens and reads it itself -- so this is
the actual integration point: call this once PROXY is ready, then pass
OUTPUT-PATH to OPEN-TONLIB exactly as you would GLOBAL-CONFIG-PATH itself.
Everything before the final WRITE-FILE-STRING here (reading, parsing,
CONFIG-WITH-LITESERVERS) is the same pure transform as
PROXY-LITESERVER-CONFIG; only the read and the write are side effects."
  (let* ((parsed (let ((jonathan:*false-value* :false) (jonathan:*null-value* :null))
                  (jonathan:parse (uiop:read-file-string global-config-path) :as :hash-table)))
         (routed (proxy-liteserver-config proxy parsed)))
    (with-open-file (out output-path :direction :output :if-exists :supersede :if-does-not-exist :create)
      (write-string (jonathan:to-json routed) out))
    output-path))

(defun check-routed-config (path)
  "Signal TON-ERROR unless the global config at PATH names exactly one liteserver
and that one is on 127.0.0.1.  Returns PATH.  This is the guarantee that a tonlib
opened on PATH can reach nothing but the local proxy."
  (let* ((parsed (json-decode (uiop:read-file-string path)))
         (servers (append (json-get parsed "liteservers") (json-get parsed "liteservers_v2"))))
    (unless (and (= (length servers) 1)
                 (eql (json-get (first servers) "ip") (ipv4-string->ip-int "127.0.0.1")))
      (ton-error "routed config must name exactly one 127.0.0.1 liteserver, got ~D entr~:@P"
                 (length servers)))
    path))

(defun %native-of (proxy)
  (etypecase proxy
    (lisp-proxy proxy)
    (proxy-liteserver (proxy-liteserver-native proxy))))

(defun proxy-ok-count (proxy method)
  "How many queries named METHOD the native PROXY's upstreams answered, in total (0 for the binary)."
  (let ((native (%native-of proxy)) (n 0))
    (when native
      (dolist (u (lisp-proxy-upstreams native) n)
        (sb-thread:with-mutex ((lisp-proxy-lock native))
          (maphash (lambda (k v) (when (and (string= (first k) method) (eq (second k) :ok)) (incf n v)))
                   (proxy-upstream-outcomes u)))))))

(defun proxy-progress-function (proxy)
  "A function for TONLIB-SYNC's PROGRESS: the number of block proofs the native PROXY has
obtained so far (every one is a step of tonlib's verified chain).  NIL for the released binary,
which has no such counter -- the sync is then simply retried a fixed number of times."
  (and (%native-of proxy) (lambda () (proxy-ok-count proxy "getBlockProof"))))

(defun open-tonlib-via-proxy (proxy global-config-path &key library-path (verbosity 0)
                                                           (keystore :in-memory) (sync t) output-path)
  "Phase E.  Route a tonlib client through PROXY (either implementation): write
GLOBAL-CONFIG-PATH's JSON with its liteservers replaced by PROXY's single
127.0.0.1 entry (PROXY-LITESERVER-GLOBAL-CONFIG-PATH), then OPEN-TONLIB on that.
Returns (VALUES TONLIB ROUTED-CONFIG-PATH).  The routed config is checked to name
exactly one liteserver, on loopback, before tonlib ever sees it: a tonlib that
could reach anything else would defeat the point of the proxy (and of tests that
must touch no real network)."
  (let* ((out (or output-path
                  (merge-pathnames "tonlib-via-proxy.global.json"
                                   (uiop:ensure-directory-pathname (proxy-liteserver-db proxy)))))
         (path (proxy-liteserver-global-config-path proxy global-config-path out)))
    (check-routed-config path)
    (values (open-tonlib path :library-path library-path :verbosity verbosity
                              :keystore keystore :sync sync
                              :sync-progress (proxy-progress-function proxy))
            path)))

(defun proxy-liteserver-alive-p (proxy)
  (and proxy
       (if (proxy-liteserver-native proxy)
           (native-proxy-alive-p (proxy-liteserver-native proxy))
           (and (proxy-liteserver-process proxy)
                (uiop:process-alive-p (proxy-liteserver-process proxy))))))

(defvar *proxy-liteserver-implementation* :native
  "Which proxy-liteserver OPEN-PROXY-LITESERVER starts by default: :NATIVE (the
Lisp implementation in this file) or :BINARY (the released executable).")

(defun open-proxy-liteserver (&key binary global-config db (port 0) (ready-timeout 10) log-file
                                (implementation *proxy-liteserver-implementation*) log)
  "Start a proxy-liteserver against GLOBAL-CONFIG with DB as its identity
directory and return a PROXY-LITESERVER struct (same shape for both
implementations).  IMPLEMENTATION is :NATIVE (default; BINARY is ignored) or
:BINARY (BINARY required: the released executable is supervised as a child
process).  See %OPEN-BINARY-PROXY-LITESERVER for the binary's parameter
semantics; the native one accepts PORT 0 on a first launch to mean 'pick a
free port and remember it'."
  (ecase implementation
    (:binary
     (%open-binary-proxy-liteserver :binary binary :global-config global-config :db db :port port
                                    :ready-timeout ready-timeout :log-file log-file))
    (:native
     (unless global-config (ton-error "GLOBAL-CONFIG is required"))
     (unless db (ton-error "DB is required: a persistent directory for proxy-liteserver's own identity"))
     (unless (probe-file global-config) (ton-error "global-config ~A does not exist" global-config))
     (let ((dir (uiop:ensure-directory-pathname db)))
       (handler-case (uiop:ensure-all-directories-exist (list dir))
         (error (e) (ton-error "could not create proxy-liteserver db directory ~A: ~A" dir e))))
     (let* ((lp (open-native-proxy :global-config global-config :db db :port port :log log))
            (proxy (make-proxy-liteserver :native lp :db db :global-config global-config
                                          :port (adnl-ext-server-port (lisp-proxy-server lp)))))
       (setf (proxy-liteserver-port proxy) (nth-value 0 (read-proxy-liteserver-identity proxy)))
       proxy))))

(defun %open-binary-proxy-liteserver (&key binary global-config db (port 0) (ready-timeout 10) log-file)
  "Launch BINARY (a proxy-liteserver executable) against GLOBAL-CONFIG,
using DB as its persistent identity/keyring directory (created if it
doesn't exist), and wait up to READY-TIMEOUT seconds for it to have
written its own <db>/config.json.

PORT matches proxy-liteserver's own '-p' semantics exactly: it is only
honored -- and only needed -- on DB's first launch, when the process picks
and remembers a port; pass 0 (the default) on every later launch reusing
an existing DB, where the port from that first run persists regardless of
what's passed here.

LOG-FILE captures the process's combined stdout+stderr; defaults to
<db>/proxy-liteserver.log so nothing is silently discarded.

Returns a PROXY-LITESERVER struct once ready to use with
PROXY-LITESERVER-CONFIG. All of the actual network work -- opening and
holding ADNL sessions to every liteserver GLOBAL-CONFIG names, deciding
which to answer a query from -- happens inside the launched process; this
function only ever touches its OS-process lifecycle and its config.json."
  (unless binary (ton-error "BINARY is required: path to the proxy-liteserver executable"))
  (unless global-config (ton-error "GLOBAL-CONFIG is required"))
  (unless db (ton-error "DB is required: a persistent directory for proxy-liteserver's own identity"))
  (validate-proxy-liteserver-preconditions binary global-config db)
  (let ((first-launch-p (not (probe-file (merge-pathnames "config.json" (uiop:ensure-directory-pathname db))))))
    (when (and first-launch-p (not (plusp port)))
      (ton-error "DB (~A) has no identity yet: PORT is required on a database's first launch ~
                 (proxy-liteserver's own '-p' semantics)" db)))
  (let* ((log-file (or log-file (merge-pathnames "proxy-liteserver.log" (uiop:ensure-directory-pathname db))))
         (args (append (list (namestring binary) "-C" (namestring global-config) "-D" (namestring db))
                       (when (plusp port) (list "-p" (write-to-string port)))))
         (process (handler-case (uiop:launch-program args :output log-file :error-output :output)
                    (error (e) (ton-error "could not launch proxy-liteserver (~A): ~A" binary e))))
         (proxy (make-proxy-liteserver :process process :binary binary :db db :global-config global-config)))
    (loop with deadline = (+ (get-internal-real-time) (* ready-timeout internal-time-units-per-second))
          until (probe-file (proxy-liteserver-config-file proxy))
          do (unless (uiop:process-alive-p process)
               (multiple-value-bind (exited-p code)
                   (ignore-errors (uiop:wait-process process))
                 (declare (ignore exited-p))
                 (ton-error "proxy-liteserver exited~@[ (exit code ~D)~] before writing ~A -- check ~A"
                            code (proxy-liteserver-config-file proxy) log-file)))
             (when (> (get-internal-real-time) deadline)
               (close-proxy-liteserver proxy)
               (ton-error "proxy-liteserver did not write ~A within ~As (still running) -- check ~A; ~
                          this is not a network problem (the identity file is written before any ~
                          liteserver connection is attempted) -- see a stuck filesystem, a sandboxed/~
                          read-only DB, or the process being frozen by something like a debugger or a ~
                          container pause"
                          (proxy-liteserver-config-file proxy) ready-timeout log-file))
             (sleep 0.1))
    (setf (proxy-liteserver-port proxy) (nth-value 0 (read-proxy-liteserver-identity proxy)))
    proxy))

(defun executable-file-p (path)
  "True when PATH exists and this process can execute it. SB-POSIX:ACCESS
returns 0 on success but SIGNALS (rather than returning a false value) when
access is denied, so this wraps it into a plain boolean."
  (and (probe-file path)
       (handler-case (zerop (sb-posix:access (namestring path) sb-posix:x-ok))
         (error () nil))))

(defun validate-proxy-liteserver-preconditions (binary global-config db)
  "Fail fast and specifically, before ever forking BINARY, on the three
things that otherwise surface only as an opaque 'exited before writing
config.json' or a full READY-TIMEOUT wait with nothing to show for it:
BINARY missing or not executable, GLOBAL-CONFIG missing, or DB not
actually writable by this process (creatable is not the same thing --
e.g. a parent directory owned by another user, or a read-only bind mount)."
  (unless (probe-file binary)
    (ton-error "proxy-liteserver-binary ~A does not exist" binary))
  (unless (executable-file-p binary)
    (ton-error "proxy-liteserver-binary ~A is not executable (chmod +x it -- a build via ~
               builder.lisp's :DEPLOY TON-TRADER-ENV hook sets this automatically, so this ~
               usually means the binary was copied/extracted another way afterward)" binary))
  (unless (probe-file global-config)
    (ton-error "global-config ~A does not exist" global-config))
  (let ((dir (uiop:ensure-directory-pathname db)))
    (handler-case (uiop:ensure-all-directories-exist (list dir))
      (error (e) (ton-error "could not create proxy-liteserver db directory ~A: ~A" dir e)))
    (let ((probe (merge-pathnames (format nil ".write-test-~A" (random most-positive-fixnum)) dir)))
      (handler-case
          (progn (with-open-file (s probe :direction :output :if-exists :supersede) (write-char #\x s))
                 (delete-file probe))
        (error (e)
          (ton-error "proxy-liteserver db directory ~A exists but is not writable by this process ~
                     (~A) -- check its ownership and permissions, and that it isn't a read-only mount"
                     dir e))))))

(defun %wait-for-process-exit (process timeout)
  "Poll until PROCESS is no longer alive, at most TIMEOUT seconds; true once
it has exited.  (UIOP:WAIT-PROCESS takes no :TIMEOUT in the ASDF that ships
with SBCL 2.6.8 -- passing one signals inside IGNORE-ERRORS, so the old
'wait' returned at once and CLOSE-PROXY-LITESERVER could return before the
child had actually died.)"
  (loop repeat (max 1 (ceiling (* timeout 20)))
        while (uiop:process-alive-p process)
        do (sleep 1/20))
  (not (uiop:process-alive-p process)))

(defun close-proxy-liteserver (proxy &key (timeout 5))
  "Terminate PROXY's OS process. Idempotent, and safe to call on an
already-dead or NIL PROXY. Escalates to a hard kill if graceful
termination hasn't finished within TIMEOUT (e.g. under heavy system
load) rather than returning with the process still alive; returns only
once the process has exited (or the hard kill's own TIMEOUT has passed)."
  (when (and proxy (proxy-liteserver-native proxy))
    (close-native-proxy (proxy-liteserver-native proxy)))
  (when (and proxy (proxy-liteserver-process proxy))
    (let ((process (proxy-liteserver-process proxy)))
      (ignore-errors (uiop:terminate-process process))
      (unless (%wait-for-process-exit process timeout)
        (ignore-errors (uiop:terminate-process process :urgent t))
        (%wait-for-process-exit process timeout)))))

;;; ===========================================================================
;;; NATIVE implementation (Phase D dispatcher)
;;; ===========================================================================

(defun proxy-stat (proxy key)
  (sb-thread:with-mutex ((lisp-proxy-lock proxy))
    (incf (gethash key (lisp-proxy-stats proxy) 0))))

(defun proxy-stat-value (proxy key)
  (sb-thread:with-mutex ((lisp-proxy-lock proxy))
    (gethash key (lisp-proxy-stats proxy) 0)))

;;; --- identity on disk (binary-compatible) -----------------------------------

(defun %keyring-path (db short-id)
  (merge-pathnames (format nil "keyring/~A" (string-upcase (octets->hex short-id)))
                   (uiop:ensure-directory-pathname db)))

(defun write-native-proxy-identity (db keypair port)
  (let ((db (uiop:ensure-directory-pathname db)))
    (ensure-directories-exist (merge-pathnames "keyring/" db))
    (let ((kr (%keyring-path db (adnl-short-id (keypair-public keypair)))))
      (with-open-file (o kr :direction :output :if-exists :supersede :element-type '(unsigned-byte 8))
        (write-sequence (tl-encode (tl-make "pk.ed25519" :key (coerce (keypair-secret keypair) 'tl-octets))) o)))
    (with-open-file (o (merge-pathnames "config.json" db) :direction :output :if-exists :supersede)
      (format o "{~%   \"@type\" : \"proxyLiteserver.config\",~%   \"port\" : ~D,~%   \"id\" : {~%      \"@type\" : \"pub.ed25519\",~%      \"key\" : \"~A\"~%   }~%}~%"
              port (base64-encode (keypair-public keypair))))))

(defun read-native-proxy-keypair (db id-base64)
  "The keypair for the identity recorded in DB's config.json, loaded from the keyring."
  (let* ((pub (base64-decode id-base64))
         (kr (%keyring-path db (adnl-short-id pub))))
    (unless (probe-file kr)
      (ton-error "keyring entry ~A for the proxy identity is missing" kr))
    (let* ((raw (with-open-file (i kr :element-type '(unsigned-byte 8))
                  (let ((v (make-array (file-length i) :element-type '(unsigned-byte 8))))
                    (read-sequence v i) v)))
           (kp (seed->keypair (subseq raw 4 36))))
      (unless (equalp (keypair-public kp) (coerce pub 'octets))
        (ton-error "keyring entry ~A does not match the public key in config.json" kr))
      kp)))

;;; --- QueryInfo: classify a query enough to honor slice limits ----------------

(defstruct (qinfo (:copier nil))
  (name "unknown") (workchain -1) (shard (- (expt 2 63)))
  seqno lt utime account-hash)

(defun %unsigned64 (v) (ldb (byte 64 0) v))

(defun qinfo-descriptor (q)
  "The text the released binary prints for a query it cannot route:
name (workchain,shard-hex)."
  (format nil "~A (~D,~(~16,'0X~))" (qinfo-name q) (qinfo-workchain q) (%unsigned64 (qinfo-shard q))))

(defun %decode-function (fn-octets)
  "The decoded liteServer function in FN-OCTETS, or (CONSTRUCTOR-ID . FN-OCTETS) when the schema
does not know it."
  (handler-case (tl-decode fn-octets)
    (error () (cons (if (>= (length fn-octets) 4)
                        (logior (aref fn-octets 0) (ash (aref fn-octets 1) 8)
                                (ash (aref fn-octets 2) 16) (ash (aref fn-octets 3) 24))
                        0)
                    fn-octets))))

(defun proxy-query-info (fn)
  "FN is a decoded liteServer function (a TL-OBJ) or an undecoded (id . raw)."
  (if (not (tl-obj-p fn))
      ;; a function the schema does not know: name it by its constructor id, so the diagnostics
      ;; say WHICH query it was
      (make-qinfo :name (if (and (consp fn) (integerp (car fn)) (plusp (car fn)))
                            (format nil "unknown-~8,'0X" (car fn))
                            "unknown"))
      (let* ((full (tl-obj-name fn))
             (name (subseq full (1+ (position #\. full :from-end t))))
             (q (make-qinfo :name name)))
        (flet ((from-block (b)
                 (when (tl-obj-p b)
                   (setf (qinfo-workchain q) (tl-get b :workchain)
                         (qinfo-shard q) (tl-get b :shard)
                         (qinfo-seqno q) (tl-get b :seqno))))
               (from-account (a)
                 (when (tl-obj-p a)
                   (setf (qinfo-workchain q) (tl-get a :workchain)
                         (qinfo-account-hash q) (tl-get a :id)))))
          (cond
            ((member full '("liteServer.getBlock" "liteServer.getBlockHeader" "liteServer.getAllShardsInfo"
                            "liteServer.getShardInfo" "liteServer.listBlockTransactions"
                            "liteServer.getConfigAll" "liteServer.getConfigParams")
                     :test #'string=)
             (from-block (tl-get fn :id)))
            ((member full '("liteServer.getAccountState" "liteServer.runSmcMethod" "liteServer.getOneTransaction")
                     :test #'string=)
             (from-block (tl-get fn :id))
             (from-account (tl-get fn :account))
             (setf (qinfo-shard q) (- (expt 2 63))))
            ((string= full "liteServer.getTransactions")
             (from-account (tl-get fn :account))
             (setf (qinfo-lt q) (tl-get fn :lt)
                   (qinfo-shard q) (- (expt 2 63))))
            ((string= full "liteServer.lookupBlock")
             (from-block (tl-get fn :id))
             (setf (qinfo-lt q) (tl-get fn :lt) (qinfo-utime q) (tl-get fn :utime))))
          q))))

(defun %shard-contains-p (shard account-hash)
  "SHARD is the signed shard id; ACCOUNT-HASH the 32 account octets."
  (let* ((s (%unsigned64 shard))
         (lowbit (logand s (- s)))
         (mask (logand (lognot (1- (* 2 lowbit))) #xFFFFFFFFFFFFFFFF))
         (acct-prefix (octets->uint account-hash :end 8)))
    (= (logand acct-prefix mask) (logand (- s lowbit) mask))))

(defun %slice-covers-p (slice q)
  "SLICE is a plist (:shards ((wc . shard) ...) :mc-seqno (min . max) :lt (min . max))."
  (let ((shards (getf slice :shards)))
    (and (or (null shards)
             (some (lambda (sh)
                     (and (eql (car sh) (qinfo-workchain q))
                          (or (null (qinfo-account-hash q))
                              (%shard-contains-p (cdr sh) (qinfo-account-hash q)))))
                   shards))
         (let ((range (getf slice :mc-seqno)))
           (or (null range) (null (qinfo-seqno q))
               (<= (or (car range) 0) (qinfo-seqno q) (or (cdr range) most-positive-fixnum))))
         (let ((range (getf slice :lt)))
           (or (null range) (null (qinfo-lt q))
               (<= (or (car range) 0) (qinfo-lt q) (or (cdr range) most-positive-fixnum)))))))

(defun upstream-accepts-p (up q)
  "Full servers (no advertised slices) accept everything; a server that
advertises slices only takes queries some slice covers."
  (let ((slices (proxy-upstream-slices up)))
    (or (null slices) (some (lambda (s) (%slice-covers-p s q)) slices))))

(defun parse-liteserver-slices (entry)
  (let ((slices (json-get entry "slices")))
    (when (and slices (listp slices))
      (loop for s in slices
            collect (list :shards (loop for sh in (json-get s "shards")
                                        collect (cons (json-get sh "workchain") (json-get sh "shard")))
                          :mc-seqno (when (or (json-get s "mc_seqno_min") (json-get s "mc_seqno_max"))
                                      (cons (json-get s "mc_seqno_min") (json-get s "mc_seqno_max")))
                          :lt (when (or (json-get s "lt_min") (json-get s "lt_max"))
                                (cons (json-get s "lt_min") (json-get s "lt_max"))))))))

;;; --- select-server -----------------------------------------------------------

(defun proxy-alive-upstreams (proxy q)
  (loop for up in (lisp-proxy-upstreams proxy)
        when (and (adnl-ext-client-alive-p (proxy-upstream-client up))
                  (upstream-accepts-p up q))
          collect up))

(defparameter *proxy-lagging-penalty* 30
  "Seconds an upstream that answered \"not ready / block not in db\" (a liteserver whose
shard client is behind) is avoided in favour of upstreams that did not.")

(defun proxy-upstream-penalized-p (up)
  (> (proxy-upstream-penalty-until up) (get-internal-real-time)))

(defun proxy-penalize (proxy up)
  (sb-thread:with-mutex ((lisp-proxy-lock proxy))
    (setf (proxy-upstream-penalty-until up)
          (+ (get-internal-real-time) (* *proxy-lagging-penalty* internal-time-units-per-second)))))

(defparameter *proxy-max-lag* 10
  "How many masterchain blocks (about 5 s each) behind the best upstream an upstream may be
and still be chosen.  Public liteservers include stale ones; asking one for the latest state
or a block proof yields old data or, for a waitMasterchainSeqno, a wait that only ends at the
client's timeout (a request that \"timed out after 120 s\").")

(defun proxy-fresh-upstreams (proxy candidates)
  "CANDIDATES whose last-known seqno is within *PROXY-MAX-LAG* of the best known one; all of
them while nothing is known yet (the pollers learn it within a couple of seconds)."
  (let ((best (sb-thread:with-mutex ((lisp-proxy-lock proxy)) (lisp-proxy-global-max-seqno proxy))))
    (if (zerop best)
        candidates
        (or (remove-if (lambda (up) (< (proxy-upstream-seqno up) (- best *proxy-max-lag*))) candidates)
            candidates))))

(defun select-server (proxy q &optional wait-seqno exclude)
  "A random alive upstream that accepts Q and is not in EXCLUDE, or NIL.
  * upstreams that recently answered \"not ready\" (PROXY-PENALIZE) are used only when no
    other is left;
  * upstreams more than *PROXY-MAX-LAG* blocks behind the best known one are avoided;
  * with WAIT-SEQNO (the client asked to wait for that masterchain seqno) upstreams already
    known to be at or past it are preferred -- they answer at once -- and when none is, the
    most advanced ones, so a stale upstream is never the one made to wait."
  (let* ((candidates (remove-if (lambda (up) (member up exclude)) (proxy-alive-upstreams proxy q)))
         (healthy (remove-if #'proxy-upstream-penalized-p candidates))
         (base (proxy-fresh-upstreams proxy (or healthy candidates)))
         (ahead (and wait-seqno
                     (remove-if-not (lambda (up) (>= (proxy-upstream-seqno up) wait-seqno)) base)))
         (pool (or ahead
                   (and wait-seqno base
                        (let ((top (reduce #'max base :key #'proxy-upstream-seqno)))
                          (remove-if-not (lambda (up) (= (proxy-upstream-seqno up) top)) base)))
                   base)))
    (and pool (proxy-pick-weighted pool))))

(defun proxy-upstream-weight (up)
  "How much UP is preferred among otherwise equal candidates: faster than typical (SLOWNESS
below 1) and with no recent failures weighs more.  Never zero, so every upstream is still tried
now and then and a recovered one is noticed."
  (let ((slow (or (proxy-upstream-slowness up) 1.0)))
    (/ 1.0 (* (expt (max 0.25 (min 4.0 slow)) 2) (1+ (proxy-upstream-fail-streak up))))))

(defun proxy-pick-weighted (pool)
  (let* ((weights (mapcar #'proxy-upstream-weight pool))
         (r (random (reduce #'+ weights))))
    (loop for up in pool for w in weights
          do (decf r w) (when (<= r 0) (return up))
          finally (return (car (last pool))))))

;;; --- seqno watermarking ------------------------------------------------------

(defun proxy-note-seqno (proxy up seqno)
  (when (and seqno (integerp seqno))
    (sb-thread:with-mutex ((lisp-proxy-lock proxy))
      (setf (proxy-upstream-seqno up) (max (proxy-upstream-seqno up) seqno)
            (lisp-proxy-global-max-seqno proxy) (max (lisp-proxy-global-max-seqno proxy) seqno)))))

(defun proxy-learn-from-answer (proxy up answer)
  "Update UP's watermark from a masterchainInfo / masterchainInfoExt /
accountState / runMethodResult answer."
  (let ((obj (handler-case (tl-decode answer) (error () nil))))
    (when (tl-obj-p obj)
      (cond ((or (tl-is obj "liteServer.masterchainInfo") (tl-is obj "liteServer.masterchainInfoExt"))
             (let ((last (tl-get obj :last)))
               (when (tl-obj-p last) (proxy-note-seqno proxy up (tl-get last :seqno)))))
            ((or (tl-is obj "liteServer.accountState") (tl-is obj "liteServer.runMethodResult"))
             (let ((id (tl-get obj :id)))
               (when (and (tl-obj-p id) (eql (tl-get id :workchain) -1))
                 (proxy-note-seqno proxy up (tl-get id :seqno))))))))
  answer)

(defun proxy-rewrite-wait (proxy up wait-seqno wait-timeout-ms elapsed-ms)
  "The outbound prefix octets (possibly empty) for a client wait request,
given the chosen upstream UP.
  * UP already known to be at or past the requested seqno -> the prefix is dropped
    (it can answer immediately);
  * otherwise the wait is forwarded UNCHANGED, with whatever is left of the client's
    timeout, so the upstream really waits for the block (and answers 652 \"timeout\"
    if it never comes) -- the released binary behaves the same way for a single
    upstream.  The wait is never clamped down to what UP happens to have: that would
    answer a client that is waiting for a new block with stale state at once.
SELECT-SERVER already prefers upstreams that are ahead, so a forwarded wait means
no known upstream has the block yet."
  (declare (ignore proxy))
  (if (>= (proxy-upstream-seqno up) wait-seqno)
      (make-array 0 :element-type '(unsigned-byte 8))
      (tl-encode (tl-make "liteServer.waitMasterchainSeqno"
                          :seqno wait-seqno
                          :timeout-ms (max 0 (- wait-timeout-ms elapsed-ms))))))

;;; --- freshness pollers ---------------------------------------------------------
;;;
;;; Seqno watermarks used to be learned only from answers to client queries, so right after
;;; start (and for upstreams nobody had asked yet) every server looked equally good -- and a
;;; stale one asked to WAIT for a new block blocked the client for the whole wait timeout.
;;; One light thread per upstream now asks it getMasterchainInfo every
;;; *PROXY-POLL-INTERVAL* seconds while it is alive; the answer feeds PROXY-LEARN-FROM-ANSWER
;;; like any other.  A poll that fails is simply not learned from (the upstream then falls
;;; behind the best one and is avoided by SELECT-SERVER once others are known).

(defparameter *proxy-poll-interval* 2
  "Seconds between freshness polls of each alive upstream.")

(defun %proxy-record-poll (up state detail)
  "Record the outcome of one freshness poll on UP; returns T when STATE/DETAIL differ
from the previous outcome in kind (so the caller logs transitions, not every poll)."
  (let ((changed (not (and (eq state (proxy-upstream-poll-state up))
                           (or (eq state :ok) (equal detail (proxy-upstream-poll-detail up)))))))
    (setf (proxy-upstream-poll-state up) state
          (proxy-upstream-poll-detail up) detail
          (proxy-upstream-poll-at up) (get-universal-time))
    (incf (proxy-upstream-polls up))
    (when (eq state :ok) (incf (proxy-upstream-polls-ok up)))
    changed))

(defun proxy-poll-upstream (proxy up)
  (let ((client (proxy-upstream-client up)))
    (handler-case
        (let* ((answer (adnl-ext-client-send-query
                        client
                        (tl-encode (tl-make "liteServer.query"
                                            :data (tl-encode (tl-make "liteServer.getMasterchainInfo"))))
                        4))
               (obj (handler-case (tl-decode answer) (error () nil))))
          (proxy-learn-from-answer proxy up answer)
          (cond ((and (tl-obj-p obj) (tl-is obj "liteServer.error"))
                 (let ((detail (format nil "liteServer.error ~A ~S" (tl-get obj :code) (tl-get obj :message))))
                   (when (%proxy-record-poll up :error detail)
                     (%client-event client "getMasterchainInfo answered with ~A" detail))))
                ((and (tl-obj-p obj) (or (tl-is obj "liteServer.masterchainInfo")
                                         (tl-is obj "liteServer.masterchainInfoExt")))
                 (let* ((last (tl-get obj :last))
                        (seqno (and (tl-obj-p last) (tl-get last :seqno))))
                   (when (%proxy-record-poll up :ok seqno)
                     (%client-event client "getMasterchainInfo answered: masterchain seqno ~A" seqno))))
                (t
                 (let ((detail (format nil "unexpected answer (~D octets, not a masterchainInfo)" (length answer))))
                   (when (%proxy-record-poll up :error detail)
                     (%client-event client "getMasterchainInfo: ~A" detail))))))
      (error (e)
        (let ((detail (princ-to-string e)))
          (when (%proxy-record-poll up :error detail)
            (%client-event client "getMasterchainInfo failed: ~A" detail)))))))

(defun start-proxy-poller (proxy up)
  (sb-thread:make-thread
   (lambda ()
     (loop until (lisp-proxy-stop-p proxy)
           do (if (adnl-ext-client-alive-p (proxy-upstream-client up))
                  (progn (setf (lisp-proxy-ever-alive-p proxy) t)
                         (proxy-poll-upstream proxy up)
                         (loop repeat (* 4 *proxy-poll-interval*)
                               until (lisp-proxy-stop-p proxy) do (sleep 0.25)))
                  (sleep 0.25))))
   :name (format nil "proxy freshness poll ~A" (proxy-upstream-name up))))

(defparameter *proxy-startup-grace* 3
  "Seconds a query waits for the FIRST upstream to come alive when none ever has (the proxy
accepts connections before its upstream sessions are up).  Afterwards a dead set answers at once.")

(defun proxy-await-upstream (proxy q)
  "While no upstream has ever been alive, wait up to *PROXY-STARTUP-GRACE* for one that
accepts Q; returns it or NIL."
  (loop repeat (round (* 10 *proxy-startup-grace*))
        until (or (lisp-proxy-ever-alive-p proxy) (lisp-proxy-stop-p proxy)
                  (proxy-alive-upstreams proxy q))
        do (sleep 0.1))
  (when (proxy-alive-upstreams proxy q) (setf (lisp-proxy-ever-alive-p proxy) t))
  (select-server proxy q))

;;; --- the query path ----------------------------------------------------------

(defun proxy-error-answer (message &optional (code 0))
  (tl-encode (tl-make "liteServer.error" :code code :message message)))

(defun proxy-split-query (data)
  "DATA is the octets inside liteServer.query.  Returns (VALUES wait-obj-or-NIL
function-octets): an optional waitMasterchainSeqno prefix and the rest."
  (let ((wait-id (tl-id-of "liteServer.waitMasterchainSeqno")))
    (if (and (>= (length data) 12) (= (%le-octets->integer (subseq data 0 4)) wait-id))
        (multiple-value-bind (obj rest) (tl-decode-prefix data)
          (values obj rest))
        (values nil data))))

;; liteServer.error code 651 is the liteserver's "not ready": the block / state asked for is not
;; in ITS database yet (e.g. "cannot load block ... is not in db (possibly out of sync:
;; shard_client_seqno=... ls_seqno=...)", a server whose shard client lags).  Another
;; upstream usually has it, so the proxy retries elsewhere instead of handing tonlib an
;; error a healthy upstream would not have produced.
(defun proxy-notready-answer-p (answer)
  (let ((obj (handler-case (tl-decode answer) (error () nil))))
    (and (tl-is obj "liteServer.error")
         (or (eql (tl-get obj :code) 651)
             (let ((msg (tl-get obj :message)))
               (and (stringp msg)
                    (or (search "not in db" msg) (search "out of sync" msg))))))))

(defparameter *proxy-max-attempts* 4
  "At most this many upstreams are tried for one query before the last answer is passed on.")

(defparameter *proxy-hedge-delay* 2
  "Seconds a query waits for its first upstream before a second one is asked as well, until
enough answers have been measured to adapt (see PROXY-HEDGE-DELAY).  The first attempt is NOT
cancelled: whichever valid answer arrives first wins, so a slow answer is never turned into a
failure.")

(defparameter *proxy-hedge-min* 0.5 "Lower bound of the adaptive hedge delay (fast networks).")
(defparameter *proxy-hedge-max* 4.0 "Upper bound of the adaptive hedge delay (slow networks).")

(defparameter *proxy-failure-penalty* 10
  "Seconds an upstream that timed out or lost its connection on a query is avoided.  It doubles
with every consecutive failure (10, 20, 40, ...) up to *PROXY-FAILURE-PENALTY-MAX*, and an answer
clears it.")

(defparameter *proxy-failure-penalty-max* 120)

(defparameter *proxy-history-queries*
  '("getBlockProof" "getBlock" "getBlockHeader" "lookupBlock" "getState" "getShardBlockProof"
    "getAllShardsInfo" "getShardInfo" "getConfigAll" "getConfigParams" "listBlockTransactions"
    "listBlockTransactionsExt")
  "Read-only queries about a block or its history.  A liteserver that has pruned, or never had,
the block answers with an ERROR for them while another may hold it, so an error answer is retried
on a different upstream (a block proof chain from the init block is hundreds of these in a row,
and tonlib restarts the whole synchronisation when one fails).  Account queries are not listed:
their errors (and exit codes) are answers about the account, the same on every server.")

(defun proxy-history-query-p (q)
  (and (member (qinfo-name q) *proxy-history-queries* :test #'string=) t))

(defun %collapse-digits (text)
  "TEXT with every run of 3+ digits replaced by # (seqnos, hashes in error messages vary per query)."
  (with-output-to-string (out)
    (let ((i 0) (n (length text)))
      (loop while (< i n)
            do (let ((c (char text i)))
                 (if (digit-char-p c)
                     (let ((j (or (position-if-not #'digit-char-p text :start i) n)))
                       (if (>= (- j i) 3) (write-char #\# out) (write-string text out :start i :end j))
                       (setf i j))
                     (progn (write-char c out) (incf i))))))))

(defun proxy-record-outcome (proxy up q outcome &optional detail)
  "Count one query outcome (:OK :TIMEOUT :DEAD :NOTREADY :ERROR) by method on UP; DETAIL is
the error text for :ERROR / :NOTREADY (digit runs collapsed, truncated)."
  (let ((key (list (qinfo-name q) outcome
                   (and detail (let ((d (%collapse-digits detail)))
                                 (subseq d 0 (min 70 (length d))))))))
    (sb-thread:with-mutex ((lisp-proxy-lock proxy))
      (incf (gethash key (proxy-upstream-outcomes up) 0)))))

(defun %note-latency (table method secs lock &optional slow-limit)
  (sb-thread:with-mutex (lock)
    (let ((cell (or (gethash method table)
                    (setf (gethash method table) (list 0 0.0 0.0 0)))))
      (incf (first cell)) (incf (second cell) secs)
      (setf (third cell) (max (third cell) secs))
      (when (and slow-limit (> secs slow-limit)) (incf (fourth cell))))))

(defun %answer-detail (answer)
  "(VALUES KIND DETAIL) for a liteServer.error ANSWER, else NIL."
  (let ((obj (handler-case (tl-decode answer) (error () nil))))
    (when (tl-is obj "liteServer.error")
      (values (tl-get obj :code)
              (format nil "~A ~A" (tl-get obj :code) (tl-get obj :message))))))

(defun proxy-query-budget (proxy wait)
  "Seconds a whole query may take: the proxy's query timeout, or longer for a wait request."
  (if wait
      (max (lisp-proxy-query-timeout proxy) (+ 1 (/ (tl-get wait :timeout-ms) 1000)))
      (lisp-proxy-query-timeout proxy)))

(defun proxy-forward (proxy up wait fn-octets started q &optional attempt-limit)
  "One attempt of a query on UP.  Returns (VALUES answer-octets retry-kind): ANSWER is
always octets (failures become liteServer.error); RETRY-KIND is :NOTREADY when UP answered
\"not ready\", :TIMEOUT when it stayed silent, :DEAD when its connection was lost (or it was
not connected), :ERROR for any other liteServer.error, else NIL.  ATTEMPT-LIMIT, when given,
caps the seconds this attempt may wait (it never raises the budget)."
  (let* ((elapsed-ms (round (* 1000 (/ (- (get-internal-real-time) started)
                                       internal-time-units-per-second))))
         (prefix (if wait
                     (proxy-rewrite-wait proxy up (tl-get wait :seqno) (tl-get wait :timeout-ms) elapsed-ms)
                     (make-array 0 :element-type '(unsigned-byte 8))))
         (payload (tl-encode (tl-make "liteServer.query" :data (%cat prefix fn-octets))))
         (budget (proxy-query-budget proxy wait))
         (budget (if attempt-limit (min budget attempt-limit) budget)))
    (handler-case
        (let* ((t-send (get-internal-real-time))
               (answer (proxy-learn-from-answer
                        proxy up (adnl-ext-client-send-query (proxy-upstream-client up) payload budget)))
               (notready (proxy-notready-answer-p answer)))
          (%note-latency (proxy-upstream-latency up) (qinfo-name q)
                         (/ (- (get-internal-real-time) t-send) (float internal-time-units-per-second))
                         (lisp-proxy-lock proxy))
          (multiple-value-bind (code detail) (%answer-detail answer)
            (cond (notready
                   (proxy-record-outcome proxy up q :notready detail)
                   (values answer :notready))
                  (code
                   (proxy-record-outcome proxy up q :error detail)
                   (values answer :error))
                  (t
                   (proxy-record-outcome proxy up q :ok)
                   (values answer nil)))))
      (adnl-timeout ()
        (proxy-stat proxy :timeout)
        (proxy-record-outcome proxy up q :timeout)
        ;; the released binary answers a silent upstream with code 652 and this exact text
        (values (proxy-error-answer "Gateway error: timeout for adnl query q" 652) :timeout))
      (adnl-closed (e)
        (proxy-stat proxy :upstream-dead)
        (proxy-record-outcome proxy up q :dead (remove #\Newline (princ-to-string e)))
        (values
         (if (typep e 'adnl-not-ready)
             (proxy-error-answer (format nil "Gateway error: ~A for query [ ~A ]"
                                         (remove #\Newline (princ-to-string e)) (qinfo-descriptor q)))
             ;; the upstream connection died WITH the query in flight: the released
             ;; binary answers code 653 and the bare text "Gateway error: " (measured
             ;; against the binary with a fakechain upstream killed mid-query)
             (proxy-error-answer "Gateway error: " 653))
         :dead)))))

(defun proxy-penalize-for (proxy up seconds)
  (sb-thread:with-mutex ((lisp-proxy-lock proxy))
    (setf (proxy-upstream-penalty-until up)
          (max (proxy-upstream-penalty-until up)
               (+ (get-internal-real-time) (* seconds internal-time-units-per-second))))))

(defun proxy-note-failure (proxy up)
  "UP timed out or lost its connection on a query: avoid it, for longer after each repeat."
  (let ((streak (sb-thread:with-mutex ((lisp-proxy-lock proxy))
                  (incf (proxy-upstream-fail-streak up)))))
    (proxy-penalize-for proxy up (min *proxy-failure-penalty-max*
                                      (* *proxy-failure-penalty* (expt 2 (min 10 (1- streak))))))))

(defun proxy-note-success (proxy up q secs)
  "UP answered Q in SECS: clear its failure streak and penalty, and update how fast it is
compared with the usual time for that method (so upstreams are comparable across methods)."
  (sb-thread:with-mutex ((lisp-proxy-lock proxy))
    (setf (proxy-upstream-fail-streak up) 0
          (proxy-upstream-penalty-until up) 0)
    (let* ((cell (or (gethash (qinfo-name q) (lisp-proxy-method-latency proxy))
                     (setf (gethash (qinfo-name q) (lisp-proxy-method-latency proxy)) (cons 0 secs))))
           (usual (max 0.05 (cdr cell)))
           (factor (max 0.25 (min 4.0 (/ secs usual)))))
      (when (>= (car cell) 3)           ; the first few answers define "usual"; do not rate against nothing
        (setf (proxy-upstream-slowness up)
              (if (proxy-upstream-slowness up)
                  (+ (* 0.7 (proxy-upstream-slowness up)) (* 0.3 factor))
                  factor)))
      (setf (cdr cell) (+ (* 0.8 (cdr cell)) (* 0.2 secs)))
      (incf (car cell)))))

(defun proxy-hedge-delay (proxy q wait)
  "Seconds to wait for the first upstream before asking a second one as well; NIL for a wait
request (those are retried one after the other, never raced).  Adapts to the measured answer time
of Q's method: slow networks wait longer, fast ones hedge sooner."
  (unless wait
    (let ((cell (sb-thread:with-mutex ((lisp-proxy-lock proxy))
                  (gethash (qinfo-name q) (lisp-proxy-method-latency proxy)))))
      (if (and cell (>= (car cell) 3))
          (max *proxy-hedge-min* (min *proxy-hedge-max* (+ 0.3 (* 1.5 (cdr cell)))))
          *proxy-hedge-delay*))))

(defun proxy-attempt (proxy up wait fn-octets started q limit)
  "PROXY-FORWARD plus the bookkeeping on UP (penalty, failure streak, speed); runs in its own
thread, so a late answer of an attempt that lost the race still teaches the proxy about UP."
  (let ((t0 (get-internal-real-time)))
    (multiple-value-bind (answer kind) (proxy-forward proxy up wait fn-octets started q limit)
      (case kind
        ((nil) (proxy-note-success proxy up q (/ (- (get-internal-real-time) t0)
                                                 (float internal-time-units-per-second))))
        (:notready (proxy-penalize proxy up))
        ((:timeout :dead) (proxy-note-failure proxy up)))
      (values answer kind))))

(defun proxy-handle-query (proxy server conn query-id query)
  "ADNL-EXT-SERVER handler: PROXY-HANDLE-QUERY-1 plus the end-to-end latency tonlib sees."
  (let* ((t0 (get-internal-real-time))
         (answer (proxy-handle-query-1 proxy server conn query-id query))
         (method (handler-case
                     (let* ((outer (tl-decode query)))
                       (qinfo-name (proxy-query-info
                                    (%decode-function (nth-value 1 (proxy-split-query (tl-get outer :data)))))))
                   (error () "?"))))
    (%note-latency (lisp-proxy-served proxy) method
                   (/ (- (get-internal-real-time) t0) (float internal-time-units-per-second))
                   (lisp-proxy-lock proxy) 8)
    answer))

(defun proxy-race (proxy q wait fn-octets history started)
  "Answer one query from the upstreams, returning the answer octets (always: failures become
liteServer.error).
  * The first attempt goes to the best upstream.  If it has not answered after the HEDGE DELAY
    (PROXY-HEDGE-DELAY) a second upstream is asked as well -- the first attempt keeps running --
    and the first VALID answer wins.  A slow answer is therefore never turned into a failure, and
    one stalled upstream costs only the hedge delay.
  * An attempt that fails outright (connection lost, \"not ready\", or -- for a block/history
    query, see *PROXY-HISTORY-QUERIES* -- any error answer) starts the next one at once.
  * At most *PROXY-MAX-ATTEMPTS* upstreams are used, and never past the query timeout (below
    what tonlib will wait: it gives up on a query after about 10 s and reconnects).
  * Wait requests are never raced, only retried one after the other.
With a single upstream there is one attempt, with the full timeout: what the released
proxy-liteserver does."
  (let* ((itu internal-time-units-per-second)
         (deadline (+ started (round (* itu (proxy-query-budget proxy wait)))))
         (sem (sb-thread:make-semaphore))
         (lock (sb-thread:make-mutex))
         (results '())                  ; (up answer kind), newest first
         (tried '()) (launched 0) (collected 0)
         (last-launch started)
         (answer nil)
         (hedge (proxy-hedge-delay proxy q wait))
         (wait-seqno (and wait (tl-get wait :seqno))))
    (labels ((now () (get-internal-real-time))
             (remaining () (/ (- deadline (now)) (float itu)))
             (pending () (- launched collected))
             (more-p ()
               (and (< launched *proxy-max-attempts*) (> (remaining) 0.2)
                    (remove-if (lambda (u) (member u tried)) (proxy-alive-upstreams proxy q))))
             (launch (up)
               (push up tried) (incf launched) (setf last-launch (now))
               (let ((limit (max 0.5 (remaining))))
                 (sb-thread:make-thread
                  (lambda ()
                    (multiple-value-bind (a kind) (proxy-attempt proxy up wait fn-octets started q limit)
                      (sb-thread:with-mutex (lock) (push (list up a kind) results))
                      (sb-thread:signal-semaphore sem)))
                  :name (format nil "proxy attempt ~A" (proxy-upstream-name up)))))
             (launch-next (stat)
               (let ((up (and (more-p) (select-server proxy q wait-seqno tried))))
                 (when up (proxy-stat proxy stat) (launch up) t)))
             (finish ()
               (return-from proxy-race
                 (or answer (proxy-error-answer "Gateway error: timeout for adnl query q" 652)))))
      (let ((first (or (select-server proxy q wait-seqno nil)
                       (and (not (lisp-proxy-ever-alive-p proxy)) (proxy-await-upstream proxy q))
                       ;; every active session is down: open the standbys now and give them a moment
                       (and (plusp (proxy-activate-standby proxy (lisp-proxy-max-active proxy)))
                            (loop repeat 30
                                  do (let ((up (select-server proxy q wait-seqno nil)))
                                       (when up (return up)))
                                     (sleep 0.1))))))
        (unless first
          (proxy-stat proxy :no-server)
          (return-from proxy-race
            (proxy-error-answer (format nil "Gateway error: no liteserver for query [ ~A ]"
                                        (qinfo-descriptor q)))))
        (launch first))
      (loop
        (let* ((hedgeable (and hedge (more-p)))
               (to-hedge (and hedgeable
                              (/ (- (+ last-launch (round (* hedge itu))) (now)) (float itu))))
               (wait-for (max 0.01 (if hedgeable (min (remaining) to-hedge) (remaining)))))
          (let ((signalled (sb-thread:wait-on-semaphore sem :timeout wait-for)))
            (if signalled
                ;; collect everything that arrived
                (let ((batch (sb-thread:with-mutex (lock) (prog1 (reverse results) (setf results '())))))
                  ;; the semaphore was decremented once; account for any further results already queued
                  (loop repeat (1- (length batch)) do (sb-thread:try-semaphore sem))
                  (dolist (r batch)
                    (destructuring-bind (up a kind) r
                      (declare (ignore up))
                      (incf collected)
                      (case kind
                        ((nil) (return-from proxy-race a))
                        (:error (setf answer a)
                         (unless history (return-from proxy-race a))
                         (launch-next :failover))
                        (t (setf answer a)
                           (launch-next :failover)))))
                  (when (and (zerop (pending)) (not (more-p))) (finish)))
                ;; nothing arrived within WAIT-FOR
                (cond ((<= (remaining) 0.0) (finish))
                      (hedgeable (launch-next :hedge))
                      (t nil)))
            (when (and (<= (remaining) 0.0) (zerop (pending))) (finish))
            (when (<= (remaining) -1.0) (finish))))))))

(defun proxy-handle-query-1 (proxy server conn query-id query)
  "The ADNL-EXT-SERVER handler: QUERY is the adnl.message.query payload.  Returns the answer
octets (always -- failures become liteServer.error); see PROXY-RACE for how upstreams are used."
  (declare (ignore server conn query-id))
  (let* ((started (get-internal-real-time))
         (outer (handler-case (tl-decode query) (error () nil))))
    (proxy-stat proxy :queries)
    (unless (tl-is outer "liteServer.query")
      (return-from proxy-handle-query-1 (proxy-error-answer "Gateway error: expected liteServer.query")))
    (multiple-value-bind (wait fn-octets) (proxy-split-query (tl-get outer :data))
      (let* ((fn (%decode-function fn-octets))
             (q (proxy-query-info fn)))
        (proxy-race proxy q wait fn-octets (proxy-history-query-p q) started)))))

;;; --- lifecycle ----------------------------------------------------------------

(defun %global-config-liteservers (parsed)
  "List of (host port pubkey-octets slices) from a parsed global config."
  (let ((entries (append (json-get parsed "liteservers") (json-get parsed "liteservers_v2"))))
    (loop for e in entries
          for ip = (json-get e "ip")
          for unsigned = (if (minusp ip) (+ ip (expt 2 32)) ip)
          collect (list (format nil "~D.~D.~D.~D" (ldb (byte 8 24) unsigned) (ldb (byte 8 16) unsigned)
                                (ldb (byte 8 8) unsigned) (ldb (byte 8 0) unsigned))
                        (json-get e "port")
                        (base64-decode (json-get (json-get e "id") "key"))
                        (parse-liteserver-slices e)))))

(defparameter *proxy-max-active-upstreams* 8
  "How many liteserver sessions the native proxy keeps open at once.  A public global config lists
a dozen or more, several of them dead or stale; keeping a session to each (with its pings and
freshness polls) costs bandwidth that matters on a weak link and buys nothing on a fast one -- a few
good upstreams are enough, and a standby is opened the moment an active one fails.")

(defun %upstream-trying-p (up)
  "UP's session is being opened and has not failed yet."
  (let ((c (proxy-upstream-client up)))
    (and (proxy-upstream-started-p up)
         (member (adnl-ext-client-stage c) '(:tcp-connecting :tcp-connected :init-sent :ack-received))
         (zerop (adnl-ext-client-failures c)))))

(defun proxy-activate-standby (proxy &optional (n 1))
  "Open the session of up to N upstreams that are on standby.  Returns how many were started."
  (let ((started 0))
    (dolist (up (lisp-proxy-upstreams proxy) started)
      (when (>= started n) (return started))
      (unless (proxy-upstream-started-p up)
        (setf (proxy-upstream-started-p up) t)
        (start-adnl-ext-client (proxy-upstream-client up))
        (incf started)))))

(defun proxy-supervise (proxy)
  "Keep (LISP-PROXY-MAX-ACTIVE PROXY) sessions alive or being opened: whenever fewer are, start a
standby (one per second, so a burst of failures does not open everything at once)."
  (sb-thread:make-thread
   (lambda ()
     (loop until (lisp-proxy-stop-p proxy)
           do (let ((live (count-if (lambda (up) (and (proxy-upstream-started-p up)
                                                      (or (adnl-ext-client-alive-p (proxy-upstream-client up))
                                                          (%upstream-trying-p up))))
                                    (lisp-proxy-upstreams proxy))))
                (when (< live (lisp-proxy-max-active proxy))
                  (proxy-activate-standby proxy 1)))
              (loop repeat 4 until (lisp-proxy-stop-p proxy) do (sleep 0.25))))
   :name "proxy supervisor"))

(defun open-native-proxy (&key global-config db (port 0) (host "127.0.0.1") (query-timeout *proxy-query-timeout*)
                            log (max-active *proxy-max-active-upstreams*))
  "Start the native proxy; returns a LISP-PROXY.  LOG, a function of (control &rest args),
receives one line per upstream event (connecting, handshake ack, first answer, each failure
with its stage and a hint); see PROXY-DIAGNOSTICS for the same information on demand.  MAX-ACTIVE
upstream sessions are opened at once (in random order, so load spreads over the public servers);
the others stand by and are opened when an active one fails (see PROXY-SUPERVISE)."
  (let* ((db (uiop:ensure-directory-pathname db))
         (config-file (merge-pathnames "config.json" db))
         (existing (probe-file config-file))
         keypair listen-port)
    (ensure-directories-exist db)
    (if existing
        (let ((parsed (json-decode (uiop:read-file-string config-file))))
          (setf keypair (read-native-proxy-keypair db (json-get (json-get parsed "id") "key"))
                listen-port (json-get parsed "port")))
        (setf keypair (adnl-generate-keypair) listen-port port))
    (let* ((proxy (%make-lisp-proxy :keypair keypair :db db :query-timeout query-timeout :log-fn log))
           (entries (%global-config-liteservers (json-decode (read-global-config global-config)))))
      (setf (lisp-proxy-max-active proxy) (max 1 max-active))
      (setf (lisp-proxy-upstreams proxy)
            (loop for (h p pub slices) in (%shuffle entries)
                  for i from 0
                  for active = (< i (lisp-proxy-max-active proxy))
                  collect (make-proxy-upstream
                           :name (format nil "~A:~D" h p) :slices slices
                           :host h :port p :public pub :started-p active
                           :client (open-adnl-ext-client h p pub :log log :start active))))
      (handler-case
          (setf (lisp-proxy-server proxy)
                (start-adnl-ext-server :keypair keypair :host host :port listen-port
                                       :handler (lambda (server conn query-id query)
                                                  (proxy-handle-query proxy server conn query-id query))))
        (error (e)
          (dolist (up (lisp-proxy-upstreams proxy)) (close-adnl-ext-client (proxy-upstream-client up)))
          (error e)))
      (let ((actual (adnl-ext-server-port (lisp-proxy-server proxy))))
        (unless existing (write-native-proxy-identity db keypair actual)))
      (setf (lisp-proxy-pollers proxy)
            (mapcar (lambda (up) (start-proxy-poller proxy up)) (lisp-proxy-upstreams proxy)))
      (setf (lisp-proxy-supervisor proxy) (proxy-supervise proxy))
      proxy)))

(defun %shuffle (list)
  (let ((v (coerce list 'vector)))
    (loop for i from (1- (length v)) downto 1
          do (rotatef (aref v i) (aref v (random (1+ i)))))
    (coerce v 'list)))

(defun close-native-proxy (proxy)
  (when proxy
    (setf (lisp-proxy-stop-p proxy) t)
    (dolist (th (cons (lisp-proxy-supervisor proxy) (lisp-proxy-pollers proxy)))
      (when th (sb-thread:join-thread th :default nil :timeout 6)))
    (stop-adnl-ext-server (lisp-proxy-server proxy))
    (dolist (up (lisp-proxy-upstreams proxy))
      (close-adnl-ext-client (proxy-upstream-client up))))
  nil)

(defun native-proxy-alive-p (proxy)
  (and proxy (lisp-proxy-server proxy)
       (not (adnl-ext-server-stop-p (lisp-proxy-server proxy)))
       (let ((th (adnl-ext-server-thread (lisp-proxy-server proxy))))
         (and th (sb-thread:thread-alive-p th)))))

(defun native-proxy-alive-upstream-count (proxy)
  (count-if (lambda (up) (adnl-ext-client-alive-p (proxy-upstream-client up)))
            (lisp-proxy-upstreams proxy)))

;;; --- diagnostics ---------------------------------------------------------------
;;;
;;; The native proxy has to work against the PUBLIC network, which a test network cannot
;;; prove.  When it does not connect, the question is always "where does it stop?":
;;;
;;;   TCP connect -> init packet -> handshake ack -> first traffic -> first query answered
;;;
;;; Every upstream client tracks which of those it reached and, on failure, the stage it
;;; failed at, the error and a one-line hint (ADNL-FAILURE-HINT).  PROXY-DIAGNOSTICS returns
;;; that as data, PROXY-DIAGNOSTICS-REPORT as text, PROXY-VERDICT condenses it into one
;;; keyword, and DIAGNOSE-PROXY runs the whole chain once against a global config.

(defun %utc-hms (universal-time)
  (if universal-time
      (multiple-value-bind (s m h) (decode-universal-time universal-time 0)
        (format nil "~2,'0D:~2,'0D:~2,'0DZ" h m s))
      "-"))

(defun %upstream-diagnostics (proxy up)
  (append (adnl-ext-client-status (proxy-upstream-client up))
          (list :seqno (proxy-upstream-seqno up)
                :polls (proxy-upstream-polls up)
                :polls-ok (proxy-upstream-polls-ok up)
                :poll-state (proxy-upstream-poll-state up)
                :poll-detail (proxy-upstream-poll-detail up)
                :poll-at (proxy-upstream-poll-at up)
                :standby (not (proxy-upstream-started-p up))
                :fail-streak (proxy-upstream-fail-streak up)
                :slowness (proxy-upstream-slowness up)
                :penalized (and (proxy-upstream-penalized-p up) t)
                :sliced (and (proxy-upstream-slices up) t)
                :latency (sb-thread:with-mutex ((lisp-proxy-lock proxy))
                           (loop for m being the hash-keys of (proxy-upstream-latency up) using (hash-value c)
                                 collect (list m (first c) (/ (second c) (max 1 (first c))) (third c))))
                :outcomes (sb-thread:with-mutex ((lisp-proxy-lock proxy))
                            (loop for (method outcome detail) being the hash-keys of (proxy-upstream-outcomes up)
                                    using (hash-value n)
                                  collect (list method outcome detail n))))))

(defun proxy-method-table (upstreams)
  "From the per-upstream plists: a list of (METHOD OK FAILED) summed over every upstream, the
method with most failures first.  FAILED counts :timeout :dead :notready and :error."
  (let ((table (make-hash-table :test 'equal)))
    (dolist (u upstreams)
      (dolist (o (getf u :outcomes))
        (destructuring-bind (method outcome detail n) o
          (declare (ignore detail))
          (let ((cell (or (gethash method table) (setf (gethash method table) (list 0 0)))))
            (if (eq outcome :ok) (incf (first cell) n) (incf (second cell) n))))))
    (sort (loop for m being the hash-keys of table using (hash-value c) collect (list m (first c) (second c)))
          (lambda (a b) (or (> (third a) (third b))
                            (and (= (third a) (third b)) (string< (first a) (first b))))))))

(defun proxy-verdict (upstreams)
  "Condense UPSTREAMS (a list of the per-upstream plists PROXY-DIAGNOSTICS returns) into
(VALUES KEYWORD ADVICE):
  :OK                 at least one upstream is connected AND answered a query
  :CONNECTED-SILENT   handshake done, but no query was answered (errors, or none yet)
  :TCP-UNREACHABLE    every upstream failed before any ADNL traffic: outbound blocked / hosts down
  :HANDSHAKE-REJECTED TCP works but the ADNL handshake does not complete (keys / middlebox)
  :STARTING           nothing has failed yet and nothing is ready: still connecting
  :NO-UPSTREAMS       the global config names no liteserver"
  (setf upstreams (remove-if (lambda (u) (getf u :standby)) upstreams))
  (flet ((get* (u k) (getf u k)))
    (cond
      ((null upstreams)
       (values :no-upstreams "the global config names no liteservers (check its \"liteservers\" list)"))
      ((some (lambda (u) (and (get* u :alive) (eq (get* u :poll-state) :ok))) upstreams)
       (values :ok "at least one upstream is connected and answering queries"))
      ((some (lambda (u) (get* u :alive)) upstreams)
       (if (some (lambda (u) (eq (get* u :poll-state) :error)) upstreams)
           (values :connected-silent
                   "handshakes complete, but the upstream(s) fail or reject getMasterchainInfo: see the per-upstream poll result")
           (values :connected-silent
                   "handshakes complete, no query answered yet (wait a poll interval, then re-check)")))
      ((every (lambda (u) (and (plusp (get* u :failures))
                               (member (second (get* u :last-failure)) '(:tcp-connecting :idle))))
              upstreams)
       (values :tcp-unreachable
               "no upstream is reachable over TCP: outbound connections to the liteserver ports are blocked, or the host has no route/DNS. Allow outbound TCP to those ip:port pairs"))
      ((some (lambda (u) (member (second (get* u :last-failure)) '(:tcp-connected :init-sent :ack-received)))
             upstreams)
       (values :handshake-rejected
               "TCP connects but the ADNL handshake never completes: the global config's public keys do not match the servers, or a middlebox/proxy is interfering with non-HTTP TCP"))
      (t (values :starting "still connecting; no upstream has failed yet")))))


(defun proxy-diagnostics (proxy)
  "A property list describing the native PROXY (a LISP-PROXY or a PROXY-LITESERVER
running :native) right now: :implementation :listen-port :verdict :advice
:global-max-seqno :stats (alist) :server (:handshakes :rejected :connections
:last-reject :closed-count :late-answers :live-conns :closed-conns) and :upstreams (one plist each, see ADNL-EXT-CLIENT-STATUS plus
:seqno :polls :polls-ok :poll-state :poll-detail :poll-at :penalized :sliced :outcomes), plus :methods
((method ok failed) ...) summed over the upstreams, most failures first.  An :outcomes entry is
(method outcome detail count) with outcome :ok :timeout :dead :notready or :error."
  (let ((native (%native-of proxy)))
    (if (null native)
        (list :implementation :binary :verdict :unknown
              :advice "the released binary has no diagnostics; use the native proxy"
              :upstreams '())
        (let* ((ups (mapcar (lambda (u) (%upstream-diagnostics native u)) (lisp-proxy-upstreams native)))
               (server (lisp-proxy-server native)))
          (multiple-value-bind (verdict advice) (proxy-verdict ups)
            (list :implementation :native
                  :listen-port (and server (adnl-ext-server-port server))
                  :verdict verdict :advice advice
                  :methods (proxy-method-table ups)
                  :served (sb-thread:with-mutex ((lisp-proxy-lock native))
                            (loop for m being the hash-keys of (lisp-proxy-served native) using (hash-value c)
                                  collect (list m (first c) (/ (second c) (max 1 (first c))) (third c) (fourth c))))
                  :global-max-seqno (lisp-proxy-global-max-seqno native)
                  :stats (sb-thread:with-mutex ((lisp-proxy-lock native))
                           (loop for k being the hash-keys of (lisp-proxy-stats native) using (hash-value v)
                                 collect (cons k v)))
                  :server (and server
                               (append
                                (sb-thread:with-mutex ((adnl-ext-server-lock server))
                                  (list :closed-count (adnl-ext-server-closed-count server)
                                        :late-answers (adnl-ext-server-late-answers server)
                                        :handshakes (adnl-ext-server-handshakes server)
                                        :rejected (adnl-ext-server-rejected server)
                                        :connections (length (adnl-ext-server-connections server))
                                        :last-reject (adnl-ext-server-last-reject server)))
                                (multiple-value-bind (live closed) (adnl-ext-server-connection-stats server)
                                  (list :live-conns live :closed-conns closed))))
                  :upstreams ups))))))

(defun %upstream-state-word (u)
  (cond ((getf u :standby) :standby)
        ((and (getf u :alive) (eq (getf u :poll-state) :ok)) :answering)
        ((getf u :alive) :connected)
        ((getf u :last-failure) :failed)
        (t :connecting)))

(defun proxy-network-summary (proxy)
  "(VALUES KEYWORD TEXT) describing the link as the proxy has experienced it: :FAST, :OK, :SLOW or
:UNKNOWN (too few queries).  Judged on the busiest method: its average answer time as tonlib saw
it (retries included) and the share of upstream attempts that failed."
  (let* ((d (proxy-diagnostics proxy))
         (served (sort (copy-list (getf d :served)) #'> :key #'second))
         (top (first served)))
    (if (or (null top) (< (second top) 5))
        (values :unknown "too few queries answered yet to judge the network")
        (destructuring-bind (method n avg mx slow) top
          (declare (ignore slow))
          (let* ((cell (find method (getf d :methods) :key #'first :test #'string=))
                 (ok (or (second cell) 0)) (bad (or (third cell) 0))
                 (fail-pct (if (plusp (+ ok bad)) (round (* 100 bad) (+ ok bad)) 0))
                 (kind (cond ((or (>= avg 2.0) (>= fail-pct 25)) :slow)
                             ((and (< avg 0.5) (< fail-pct 5)) :fast)
                             (t :ok))))
            (values kind
                    (format nil "~A: ~A answers (~D) take ~,1F s on average, ~,1F s at worst; ~D% of upstream attempts failed~A"
                            (ecase kind (:slow "slow network") (:ok "network ok") (:fast "fast network"))
                            method n avg mx fail-pct
                            (if (eq kind :slow)
                                " -- the first sync of an empty keystore will be long; later runs reuse the saved state"
                                ""))))))))

(defun proxy-diagnostics-report (proxy &key verbose)
  "PROXY-DIAGNOSTICS as a compact multi-line string: verdict + advice, a summary count, the
failures grouped by cause (stage, error, hint), then one line per upstream.  VERBOSE adds each
upstream's counters and recent event lines."
  (let* ((d (proxy-diagnostics proxy))
         (ups (getf d :upstreams)))
    (with-output-to-string (out)
      (format out "proxy-liteserver (~(~A~)) verdict: ~A~%  ~A~%"
              (getf d :implementation) (getf d :verdict) (getf d :advice))
      (when (eq (getf d :implementation) :native)
        (multiple-value-bind (kind text) (proxy-network-summary proxy)
          (unless (eq kind :unknown) (format out "  ~A~%" text))))
      (when (eq (getf d :implementation) :native)
        (let ((sv (getf d :server)))
          (format out "  listener 127.0.0.1:~A  handshakes ~A  rejected ~A  open connections ~A  best masterchain seqno ~A~%"
                  (getf d :listen-port) (getf sv :handshakes) (getf sv :rejected) (getf sv :connections)
                  (getf d :global-max-seqno))
          (when (getf sv :last-reject)
            (format out "  last rejected inbound handshake ~A: ~A -- the client did not present this proxy's key (stale routed config?)~%"
                    (%utc-hms (car (getf sv :last-reject))) (cdr (getf sv :last-reject))))
          (when (getf d :stats)
            (format out "  queries: ~{~(~A~)=~A~^ ~}~%"
                    (loop for (k . v) in (sort (copy-list (getf d :stats)) #'string< :key #'princ-to-string)
                          append (list k v)))))
        (let ((n (length ups)))
          (format out "  upstreams: ~D  answering ~D  connected-only ~D  failed ~D  connecting ~D  standby ~D~%"
                  n
                  (count :answering ups :key #'%upstream-state-word)
                  (count :connected ups :key #'%upstream-state-word)
                  (count :failed ups :key #'%upstream-state-word)
                  (count :connecting ups :key #'%upstream-state-word)
                  (count :standby ups :key #'%upstream-state-word)))
        ;; failures grouped by (stage, hint): the cause, and how many upstreams share it
        (when (getf d :served)
          (format out "  answer time as tonlib sees it, retries included (n avg/max s, >8s): ~{~A~^  ~}~%"
                  (loop for (m n avg mx slow) in (sort (copy-list (getf d :served)) #'> :key #'second)
                        collect (format nil "~A ~D ~,1F/~,1F~@[ slow ~D~]" m n avg mx (and (plusp slow) slow)))))
        (let ((sv (getf d :server)))
          (when sv
            (format out "  tonlib connections: ~D opened, ~D closed, ~D open; answers undeliverable because the client was already gone: ~D~%"
                    (getf sv :handshakes) (getf sv :closed-count) (getf sv :connections) (getf sv :late-answers))
            (dolist (c (subseq (getf sv :closed-conns) 0 (min 5 (length (getf sv :closed-conns)))))
              (format out "    closed ~A after ~Ds: ~D queries, ~D answered, ~D late, ~D in flight, slowest ~,1Fs -- ~A~%"
                      (%utc-hms (getf c :closed)) (- (getf c :closed) (getf c :opened))
                      (getf c :queries) (getf c :answered) (getf c :late) (getf c :in-flight-at-close)
                      (getf c :slowest) (getf c :reason)))))
        (when (getf d :methods)
          (format out "  queries by method (ok/failed): ~{~A~^  ~}~%"
                  (loop for (m ok bad) in (getf d :methods)
                        collect (format nil "~A ~D/~D" m ok bad))))
        (let ((groups '()))
          (dolist (u ups)
            (let ((f (and (not (getf u :alive)) (getf u :last-failure))))
              (when f
                (let ((entry (assoc (list (second f) (fourth f)) groups :test #'equal)))
                  (if entry
                      (push (getf u :name) (cdr entry))
                      (push (list (list (second f) (fourth f)) (getf u :name)) groups))))))
          (dolist (g (reverse groups))
            (destructuring-bind ((stage hint) &rest names) g
              (format out "  ~D x failed at ~(~A~): ~A~%" (length names) stage hint))))
        (dolist (u ups)
          (let ((f (getf u :last-failure)))
            (format out "- ~A  ~(~A~)  stage ~(~A~)  handshakes ~D  poll ~(~A~)~@[ (~A)~]~@[  last error: ~A~]~%"
                    (getf u :name) (%upstream-state-word u) (getf u :stage) (getf u :connects)
                    (or (getf u :poll-state) "none") (getf u :poll-detail)
                    (and f (not (getf u :alive)) (third f)))
            (let ((lat (getf u :latency)))
              (when lat
                (format out "    answer time: ~{~A~^  ~}~%"
                        (loop for (m n avg mx) in (sort (copy-list lat) #'> :key #'second)
                              collect (format nil "~A ~D ~,1F/~,1Fs" m n avg mx)))))
            (let ((bad (sort (remove :ok (copy-list (getf u :outcomes)) :key #'second)
                             #'> :key #'fourth)))
              (when bad
                (format out "    query failures: ~{~A~^; ~}~%"
                        (loop for (method outcome detail n) in (subseq bad 0 (min 4 (length bad)))
                              collect (format nil "~A ~(~A~)~@[ [~A]~] x~D" method outcome detail n)))))
            (when verbose
              (format out "    attempts ~D  failures ~D  queries ~D  answers ~D  pongs ~D  seqno ~D~%"
                      (getf u :attempts) (getf u :failures) (getf u :queries)
                      (getf u :answers) (getf u :pongs) (getf u :seqno))
              (dolist (ev (last (getf u :events) 6))
                (format out "      ~A ~A~%" (%utc-hms (car ev)) (cdr ev))))))))))

(defun proxy-wait-ready (proxy &key (timeout 20))
  "Wait up to TIMEOUT seconds until PROXY has an upstream that is connected AND answering
(verdict :OK).  Returns (VALUES READY-P VERDICT)."
  (let ((deadline (+ (get-internal-real-time) (* timeout internal-time-units-per-second)))
        (verdict nil))
    (loop
      (setf verdict (getf (proxy-diagnostics proxy) :verdict))
      (when (or (eq verdict :ok) (>= (get-internal-real-time) deadline)
                (let ((n (%native-of proxy))) (or (null n) (lisp-proxy-stop-p n))))
        (return))
      (sleep 0.2))
    (values (eq verdict :ok) verdict)))

(defun start-proxy-watch (proxy log &key (timeout 20))
  "Background thread: wait up to TIMEOUT seconds for PROXY to become ready, then pass ONE
report to LOG (a function of (control &rest args)): a one-line summary when it is, the full
report -- stage, error and hint per upstream -- when it is not.  Never blocks the caller."
  (sb-thread:make-thread
   (lambda ()
     (ignore-errors
      (multiple-value-bind (ready verdict) (proxy-wait-ready proxy :timeout timeout)
        (cond
          ((let ((n (%native-of proxy))) (or (null n) (lisp-proxy-stop-p n))) nil) ; closed meanwhile
          (ready
            (let* ((d (proxy-diagnostics proxy))
                   (ups (getf d :upstreams)))
              (funcall log "proxy-liteserver ready: ~D/~D upstream(s) answering, best masterchain seqno ~A"
                       (count-if (lambda (u) (and (getf u :alive) (eq (getf u :poll-state) :ok))) ups)
                       (length ups) (getf d :global-max-seqno))))
          (t
            (funcall log "proxy-liteserver NOT ready after ~As (~(~A~)):~%~A"
                     timeout verdict (proxy-diagnostics-report proxy)))))))
   :name "proxy-watch"))

(defparameter *diagnose-account* "Ef8zMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzMzM0vF"
  "The account read at the end of DIAGNOSE-PROXY's tonlib leg: the elector contract, which exists on
mainnet and testnet and lives in the masterchain.")

(defun diagnose-proxy (global-config &key (timeout 25) db tonlib library-path (stream *standard-output*)
                                       (sync-timeout 120) (sync-total-timeout 900) keystore
                                       (account *diagnose-account*))
  "One-shot check of the NATIVE proxy against GLOBAL-CONFIG (a path): start it on a scratch
database (or DB) and wait up to TIMEOUT seconds for an upstream to answer.  With TONLIB true,
go on to what the bot really does: open a tonlib client THROUGH the proxy, run tonlib's full
synchronisation (the block-proof chain from the config's init block; up to SYNC-TIMEOUT seconds
per attempt, 8 attempts), time it, and read one account.  The report -- verdict, per-upstream
state, queries by method and every upstream's failed queries -- is printed to STREAM and
returned.  The sync is patient (see TONLIB-SYNC): it keeps going while verified block proofs keep
arriving, up to SYNC-TOTAL-TIMEOUT seconds, and prints its progress.  KEYSTORE, a directory, keeps
tonlib's validated state between runs, so a second run after one slow first sync is quick.
ACCOUNT (an address string) is the account read at the end.  Returns (VALUES OK-P
REPORT-STRING); with TONLIB, OK-P needs the sync and the account read to succeed as well."
  (let* ((scratch (not db))
         (db (or db (format nil "~A/ton-trader-diagnose-~D-~D/"
                            (string-right-trim "/" (namestring (uiop:temporary-directory)))
                            (sb-posix:getpid) (get-universal-time))))
         (proxy nil) (tl nil) (tonlib-lines '()) (ok nil) (report ""))
    (flet ((say (control &rest args)
             (when stream
               (sb-thread:with-recursive-lock (*adnl-log-lock*)
                 (format stream "~&[~A] ~?~%" (%utc-hms (get-universal-time)) control args)
                 (finish-output stream))))
           (secs (since) (/ (- (get-internal-real-time) since) (float internal-time-units-per-second))))
      (unwind-protect
           (progn
             (setf proxy (open-proxy-liteserver
                          :implementation :native :global-config global-config :db db :port 0
                          :log (lambda (control &rest args) (apply #'say control args))))
             (multiple-value-bind (ready verdict) (proxy-wait-ready proxy :timeout timeout)
               (setf ok ready)
               (when (and ready tonlib)
                 (handler-case
                     (let ((t0 (get-internal-real-time)))
                       (setf tl (open-tonlib-via-proxy proxy global-config :library-path library-path
                                                                             :keystore (ensure-keystore keystore)
                                                                             :sync nil))
                       (say "tonlib: synchronising through the proxy (block proofs from the init block; minutes on a weak link, quick when the keystore already holds the state)...")
                       (let ((seqno (tonlib-sync tl :timeout sync-timeout :total-timeout sync-total-timeout
                                                    :progress (proxy-progress-function proxy)
                                                    :on-attempt (lambda (n e gained now)
                                                                  (declare (ignore e))
                                                                  (say "tonlib: sync attempt ~D did not finish: ~D verified step~:P gained, ~D so far"
                                                                       n gained now)))))
                         (push (format nil "tonlib sync through the proxy: masterchain seqno ~A in ~,1Fs"
                                       seqno (secs t0))
                               tonlib-lines))
                       (let* ((t1 (get-internal-real-time))
                              (st (tonlib-account-state tl (parse-address account))))
                         (push (format nil "tonlib account read through the proxy: ~A is ~(~A~), balance ~A nanoTON, in ~,1Fs"
                                       account (account-state-status st)
                                       (account-state-balance st) (secs t1))
                               tonlib-lines)))
                   (error (e)
                     (setf ok nil)
                     (push (format nil "tonlib through the proxy FAILED: ~A" e) tonlib-lines))))
               (setf report (with-output-to-string (o)
                              (write-string (proxy-diagnostics-report proxy) o)
                              (dolist (l (reverse tonlib-lines)) (format o "~A~%" l))
                              (format o "RESULT: ~A (~(~A~))~%" (if ok "OK" "FAILED") verdict)))))
        (ignore-errors (when tl (close-tonlib tl)))
        (ignore-errors (when proxy (close-proxy-liteserver proxy)))
        (when scratch (ignore-errors (uiop:delete-directory-tree (uiop:ensure-directory-pathname db)
                                                                 :validate t :if-does-not-exist :ignore)))))
    (when stream (format stream "~&~A" report) (finish-output stream))
    (values ok report)))
