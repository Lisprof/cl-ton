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

;;;; overlay-query.lisp -- queries to the members of a public overlay, without being a member (plan "Low-Level Client", Gate 1/2).
;;;;
;;;; The node answers overlay.query from ANY ADNL peer on a public overlay (OverlayImpl::check_src_peer): the query is the boxed
;;;; overlay.query {overlay} followed by the boxed function (a "prefix" query), for example tonNode.getCapabilities.  Mainnet
;;;; nodes were measured to answer it over plain ADNL UDP (a small answer) and, for bigger answers, over RLDP2 (src/rldp.lisp).
;;;; The direct tonNode.query path of the node's full-node master is not open on public nodes.
;;;;
;;;; OVERLAY-QUERY is the one transport-neutral entry point: TRANSPORT picks how the framed query travels -- :RLDP2 (default,
;;;; any answer size), :ADNL (one datagram exchange, answers up to about 8 KB), :QUIC (src/quic.lisp; HOST:PORT are then the
;;;; peer's QUIC endpoint from its adnl.address.quic, not its ADNL endpoint).

(in-package :cl-ton)

(defun overlay-id-of-shard (workchain shard zero-state-file-hash)
  "The 32-octet short id of the public overlay of a shard (FullNodeShardImpl::start_up): the sha256 of the boxed
pub.overlay whose name is the sha256 of the boxed tonNode.shardPublicOverlayId.  SHARD is the signed 64-bit shard id, for the
whole masterchain -9223372036854775808; ZERO-STATE-FILE-HASH is validator.zero_state.file_hash of the config (32 octets)."
  (let* ((name (sha256 (tl-encode (tl-make "tonNode.shardPublicOverlayId" :workchain workchain :shard shard
                                                                          :zero-state-file-hash (coerce zero-state-file-hash 'tl-octets)))))
         (pub (tl-make "pub.overlay" :name (coerce name 'tl-octets))))
    (sha256 (tl-encode pub))))

(defun overlay-query-bytes (overlay-id function)
  "The octets of the framed query: boxed overlay.query {OVERLAY-ID} then FUNCTION (a TL object or its boxed octets)."
  (concatenate 'tl-octets
               (tl-encode (tl-make "overlay.query" :overlay (coerce overlay-id 'tl-octets)))
               (if (tl-obj-p function) (tl-encode function) (coerce function 'tl-octets))))

(defun overlay-broadcast-octets (overlay-id keypair data &key (flags 0) date)
  "The octets of an adnl.message.custom payload that broadcasts DATA (octets) in the public overlay OVERLAY-ID as a plain
overlay.broadcast signed by KEYPAIR (the sender needs no membership: the overlay judges the content): the boxed overlay.message
{OVERLAY-ID} followed by the boxed overlay.broadcast {src = the key, no certificate, FLAGS, DATA, DATE (now), the signature over
overlay.broadcast.toSign{hash, date}}, hash = the sha256 of overlay.broadcast.id{short id of the key, sha256 of DATA, FLAGS}
(overlay/broadcast-simple.cpp).  A node accepts a date within 20 s of its own clock."
  (let* ((data (coerce data 'tl-octets))
         (date (or date (unix-now)))
         (hash (sha256 (tl-encode (tl-make "overlay.broadcast.id" :src (coerce (adnl-short-id (keypair-public keypair)) 'tl-octets)
                                                                   :data-hash (coerce (sha256 data) 'tl-octets) :flags flags))))
         (signature (sign-octets keypair (tl-encode (tl-make "overlay.broadcast.toSign" :hash (coerce hash 'tl-octets) :date date))))
         (broadcast (tl-make "overlay.broadcast" :src (tl-make "pub.ed25519" :key (coerce (keypair-public keypair) 'tl-octets))
                                                 :certificate (tl-make "overlay.emptyCertificate")
                                                 :flags flags :data data :date date :signature (coerce signature 'tl-octets))))
    (concatenate 'tl-octets
                 (tl-encode (tl-make "overlay.message" :overlay (coerce overlay-id 'tl-octets)))
                 (tl-encode broadcast))))

(defun external-message-broadcast-octets (message-boc)
  "The boxed tonNode.externalMessageBroadcast carrying MESSAGE-BOC (the serialized external inbound message), the DATA of an
overlay broadcast in a shard overlay."
  (tl-encode (tl-make "tonNode.externalMessageBroadcast"
                      :message (tl-make "tonNode.externalMessage" :data (coerce message-boc 'tl-octets)))))

(defun overlay-send-broadcast (node host port peer-public overlay-id keypair data &key (flags 0))
  "Send DATA as a signed overlay broadcast (OVERLAY-BROADCAST-OCTETS) to the member PEER-PUBLIC at HOST:PORT of the overlay
OVERLAY-ID over the ADNL UDP NODE: one datagram, no answer (the node rebroadcasts what it accepts to its neighbours).  T."
  (adnl-udp-send-custom node host port peer-public (overlay-broadcast-octets overlay-id keypair data :flags flags)))

(defstruct (overlay-client (:conc-name ocl-) (:constructor %make-overlay-client) (:copier nil))
  node (lock (sb-thread:make-mutex :name "overlay-client"))
  (peers (make-hash-table :test 'equalp))         ; peer short id -> OCL-PEER
  (quic-peers (make-hash-table :test 'equalp)))   ; peer short id -> OCL-QUIC-PEER

(defstruct (ocl-peer (:copier nil)) connection host port)

(defstruct (ocl-quic-peer (:copier nil)) connection socket thread host port)

(defun make-overlay-client (node)
  "A client over the ADNL UDP node NODE (see ADNL-UDP-START): installs itself as the node's custom-message handler so the
RLDP2 messages of every peer reach that peer's RLDP connection.  The node's custom handler must not be used for anything else."
  (let ((client (%make-overlay-client :node node)))
    (setf (adnl-udp-custom-handler node)
          (lambda (data public)
            (let ((peer (sb-thread:with-mutex ((ocl-lock client))
                          (gethash (adnl-short-id public) (ocl-peers client)))))
              (when peer (rldp-receive (ocl-peer-connection peer) data)))))
    client))

(defun %ocl-peer (client host port public)
  "The RLDP connection to the node PUBLIC at HOST:PORT, created on first use; its address follows the latest query."
  (sb-thread:with-mutex ((ocl-lock client))
    (let* ((id (adnl-short-id public))
           (peer (or (gethash id (ocl-peers client))
                     (let ((peer (make-ocl-peer :host host :port port)))
                       (setf (ocl-peer-connection peer)
                             (make-rldp-connection
                              (lambda (message)
                                (adnl-udp-send-custom (ocl-node client) (ocl-peer-host peer) (ocl-peer-port peer) public message))))
                       (setf (gethash id (ocl-peers client)) peer)))))
      (setf (ocl-peer-host peer) host (ocl-peer-port peer) port)
      (ocl-peer-connection peer))))

(defun %ocl-quic-peer (client host port public)
  "The QUIC connection to the node PUBLIC at its QUIC endpoint HOST:PORT, created on first use: one connected
UDP socket and one receive thread per peer (the pattern of the ADNL peer sockets), the connection authenticated
by the node's ADNL key, our own ADNL identity presented as the client certificate when asked."
  (sb-thread:with-mutex ((ocl-lock client))
    (let* ((id (adnl-short-id public))
           (peer (gethash id (ocl-quic-peers client))))
      (when (and peer (not (and (equal host (ocl-quic-peer-host peer))
                                (eql port (ocl-quic-peer-port peer)))))
        (ignore-errors (sb-bsd-sockets:socket-close (ocl-quic-peer-socket peer)))
        (setf peer nil))
      (unless peer
        (let* ((socket (make-instance 'sb-bsd-sockets:inet-socket :type :datagram :protocol :udp))
               (p (make-ocl-quic-peer :host host :port port :socket socket)))
          (sb-bsd-sockets:socket-connect socket (sb-bsd-sockets:make-inet-address host) port)
          (setf (ocl-quic-peer-connection p)
                (make-quic-connection
                 (lambda (datagram) (ignore-errors (sb-bsd-sockets:socket-send socket datagram nil)))
                 :identity-seed (keypair-secret (adnl-udp-keypair (ocl-node client)))
                 :peer-id id)
                (ocl-quic-peer-thread p)
                (sb-thread:make-thread
                 (lambda ()
                   (let ((buffer (make-array 65536 :element-type '(unsigned-byte 8))) (errors 0))
                     (loop
                       (handler-case
                           (multiple-value-bind (buf length) (sb-bsd-sockets:socket-receive socket buffer nil)
                             (declare (ignore buf))
                             (unless length (return))
                             (setf errors 0)
                             (quic-receive (ocl-quic-peer-connection p) (subseq buffer 0 length)))
                         ;; a connected UDP socket raises a queued ICMP error (e.g. ECONNREFUSED when the
                         ;; peer's port was momentarily unbound) on receive: that is transient, the error
                         ;; is consumed by the failed call, and the thread must survive it -- an unhandled
                         ;; error here would kill the whole process.  A socket that fails persistently
                         ;; (closed when the peer entry is recreated) ends the thread instead of spinning.
                         (error ()
                           (when (> (incf errors) 100) (return))
                           (sleep 0.05))))))
                 :name "quic-receive"))
          (setf (gethash id (ocl-quic-peers client)) p peer p)))
      (ocl-quic-peer-connection peer))))

(defun overlay-query (client host port peer-public overlay-id function
                      &key (transport :rldp2) (timeout 5) (max-answer-size 1048576))
  "Ask the member PEER-PUBLIC at HOST:PORT of the public overlay OVERLAY-ID to run FUNCTION (a TL object or boxed octets);
returns the answer's octets (a boxed TL object).  TRANSPORT :RLDP2 handles any answer size (signals RLDP-TIMEOUT), :ADNL only
small ones (signals ADNL-UDP-TIMEOUT), :QUIC runs over the peer's QUIC endpoint (HOST:PORT are the QUIC address then;
signals QUIC-TIMEOUT).  No membership, no registration: the node answers any peer."
  (let ((query (overlay-query-bytes overlay-id function)))
    (ecase transport
      (:rldp2 (rldp-query (%ocl-peer client host port peer-public) query :timeout timeout :max-answer-size max-answer-size))
      (:quic (quic-query (%ocl-quic-peer client host port peer-public) query :timeout timeout :max-answer-size max-answer-size))
      (:adnl (adnl-udp-query (ocl-node client) host port peer-public query :timeout timeout)))))

;;;; --- the tonNode client: a pool of untrusted peers, hedged queries, verified answers (plan phase 4) -----------------------------
;;;;
;;;; Nothing a peer says is believed: every answer goes through an ACCEPT function that returns the value or NIL, and blocks and
;;;; proofs are checked against hashes and validator signatures (sync.lisp).  Peers are unreliable and the network may be poor, so
;;;; TONNODE-CALL sends a query to HEDGE peers at once (the best by measured round trip) and takes the first acceptable answer;
;;;; a peer that is silent, wrong or does not hold the block is demoted (cool-down) and the next ones are tried.  Fast networks
;;;; lose nothing (the best peer answers first); lossy ones get redundancy.  Answers of the full nodes: the block and proof calls
;;;; return the raw BoC (first octets b5 ee 9c 72) and not a tonNode.data object (measured on mainnet 2026-11-07).

(define-condition tonnode-error (ton-error) ())

(defstruct (tn-peer (:copier nil) (:constructor make-tn-peer (host port public)))
  host port public
  (rtt nil)                              ; smoothed seconds of a successful query, NIL = not measured yet
  (ok 0) (bad 0) (streak 0)              ; answers accepted, rejected or missing; consecutive failures
  (until 0d0)                            ; cool-down end (monotonic seconds)
  (inflight 0)                           ; queries to the peer that are on their way (spreads parallel downloads over the peers)
  (lacks (make-hash-table)))             ; block seqno -> when the peer said it does not hold it

(defstruct (tonnode-pool (:conc-name tnp-) (:copier nil) (:constructor %make-tonnode-pool))
  client overlay-id peers (hedge 2) (stagger nil) (transport :rldp2) (lock (sb-thread:make-mutex :name "tonnode-pool")))

(defun make-tonnode-pool (client overlay-id peers &key (hedge 2) (stagger 2.5) (transport :rldp2))
  "A pool over the OVERLAY-CLIENT and the public overlay OVERLAY-ID; PEERS = list of (host port public-key).  HEDGE how many peers are asked
at first (see TONNODE-CALL), STAGGER (seconds, NIL for none) how long a wave of peers is waited for before the next one is started
beside it (real mainnet 2026-11-17: only about a third of the members of an overlay answer, and a query that waited for the timeout of
every silent wave took up to 36 s).  TRANSPORT is the OVERLAY-QUERY transport for every peer (default :RLDP2); with :QUIC the peers'
host/port must be their QUIC endpoints (adnl.address.quic)."
  (%make-tonnode-pool :client client :overlay-id overlay-id :hedge hedge :stagger stagger :transport transport
                      :peers (mapcar (lambda (p) (make-tn-peer (first p) (second p) (third p))) peers)))

(defun %tn-now () (/ (get-internal-real-time) (float internal-time-units-per-second 1d0)))

(defun %tn-note (pool peer status seconds)
  "Record how a query to PEER went: STATUS :OK, :EMPTY (answered, nothing to give), :LACKS, :BAD (answer rejected) or :FAIL (silence)."
  (sb-thread:with-mutex ((tnp-lock pool))
    (ecase status
      ((:ok :empty) (incf (tn-peer-ok peer)) (setf (tn-peer-streak peer) 0 (tn-peer-until peer) 0d0)
       (setf (tn-peer-rtt peer) (if (tn-peer-rtt peer) (+ (* 0.7d0 (tn-peer-rtt peer)) (* 0.3d0 seconds)) seconds)))
      (:lacks (setf (tn-peer-streak peer) 0))
      (:quiet nil)                         ; silence that is not held against the peer (a block too new to have a proof yet)
      ((:bad :fail)
       (incf (tn-peer-bad peer))
       (let ((streak (incf (tn-peer-streak peer))))
         ;; wrong data is punished harder than silence (a weak network loses packets, a liar lies)
         (when (or (eq status :bad) (>= streak 3))
           (setf (tn-peer-until peer) (+ (%tn-now) (min 300d0 (* (if (eq status :bad) 60d0 10d0) (expt 2 (min 4 (1- streak))))))))))))
  nil)

(defun %tn-rank (peer)
  "The order of PEER among the usable ones (smaller = asked first): 0 answered before and is not failing now (by round trip), 1 never
asked (by chance), 2 answered before but failed since (by the failures in a row), 3 never answered and failed (by failures).  Real
mainnet (proofmap report, fix 94): of 33 members of the masterchain overlay only about 10 ever answer; a peer that has failed twice
and never answered must not come before one that answered in 0.5 s."
  (let ((ok (tn-peer-ok peer)) (bad (tn-peer-bad peer)) (streak (tn-peer-streak peer)))
    (values (cond ((and (plusp ok) (zerop streak)) 0)
                  ((and (zerop ok) (zerop bad)) 1)
                  ((plusp ok) 2)
                  (t 3))
            (case (cond ((and (plusp ok) (zerop streak)) 0) ((and (zerop ok) (zerop bad)) 1) ((plusp ok) 2) (t 3))
              (0 (* (or (tn-peer-rtt peer) 0.3d0) (+ 1d0 (random 0.3d0)) (+ 1d0 (tn-peer-inflight peer))))
              (1 (+ (random 1d0) (tn-peer-inflight peer)))
              (2 (+ streak (random 0.5d0)))
              (t (+ bad (random 0.5d0)))))))

(defun %tn-pick (pool n tried seqno)
  "Up to N peers not in TRIED: usable ones (no cool-down, not known to lack SEQNO) in the order of %TN-RANK (peers that answered
before first, by round trip; then the ones never asked, by chance; then the ones that failed), then those in cool-down by their end."
  (let ((now (%tn-now)) (usable '()) (cooling '()))
    (sb-thread:with-mutex ((tnp-lock pool))
      (dolist (p (tnp-peers pool))
        (unless (member p tried)
          (let ((lack (and seqno (gethash seqno (tn-peer-lacks p)))))
            (cond ((and lack (< (- now lack) 300d0)))                  ; skip: it told us recently it does not hold it
                  ((> (tn-peer-until p) now) (push p cooling))
                  (t (push p usable)))))))
    (let* ((ranked (mapcar (lambda (p) (multiple-value-bind (rank key) (%tn-rank p) (list rank key p))) usable))
           (ordered (append (mapcar #'third (sort ranked (lambda (a b) (or (< (first a) (first b))
                                                                           (and (= (first a) (first b)) (< (second a) (second b)))))))
                            (sort cooling #'< :key #'tn-peer-until))))
      (subseq ordered 0 (min n (length ordered))))))

(defstruct (%tn-box (:copier nil)) (lock (sb-thread:make-mutex)) (sem (sb-thread:make-semaphore)) value peer (finished 0) (empty 0) (statuses '()))

(defun %tn-worker (pool peer function accept precheck timeout max-answer-size seqno box &optional (blame t))
  (let ((t0 (%tn-now)) (status :fail) (value nil))
    (sb-thread:with-mutex ((tnp-lock pool)) (incf (tn-peer-inflight peer)))
    (unwind-protect
         (handler-case
             (block try
               (when (and precheck (not (funcall precheck peer)))
                 (when seqno (sb-thread:with-mutex ((tnp-lock pool)) (setf (gethash seqno (tn-peer-lacks peer)) (%tn-now))))
                 (setf status :lacks) (return-from try))
               (let ((octets (overlay-query (tnp-client pool) (tn-peer-host peer) (tn-peer-port peer) (tn-peer-public peer)
                                            (tnp-overlay-id pool) function :transport (tnp-transport pool)
                                            :timeout timeout :max-answer-size max-answer-size)))
                 (multiple-value-bind (v why) (funcall accept octets)
                   (cond (v (setf value v status :ok))
                         ((eq why :empty) (setf status :empty))
                         ((eq why :lacks) (setf status :lacks))
                         (t (setf status :bad))))))
           (error () (setf status (if blame :fail :quiet))))
      (sb-thread:with-mutex ((tnp-lock pool)) (decf (tn-peer-inflight peer)))
      (%tn-note pool peer status (- (%tn-now) t0))
      (sb-thread:with-mutex ((%tn-box-lock box))
        (incf (%tn-box-finished box))
        (push status (%tn-box-statuses box))
        (when (eq status :empty) (incf (%tn-box-empty box)))
        (when (and value (null (%tn-box-value box))) (setf (%tn-box-value box) value (%tn-box-peer box) peer)))
      (sb-thread:signal-semaphore (%tn-box-sem box)))))

(defun %tn-call-staggered (pool function accept precheck timeout hedge attempts max-answer-size seqno empty-ok blame stagger)
  "TONNODE-CALL with waves that overlap: a wave of peers (HEDGE, twice as many in every further wave) that has not given an acceptable
answer within STAGGER seconds is joined by the next wave while it goes on asking; the first acceptable answer wins.  A wave whose peers
have all finished without an answer is followed at once."
  (let* ((tried '()) (box (make-%tn-box)) (launched 0)
         (overall (+ (%tn-now) timeout 1.5d0 (* (1- attempts) stagger))))
    (flet ((wait-until (limit)
             (loop
               (let ((remaining (- limit (%tn-now))))
                 (when (or (%tn-box-value box) (>= (%tn-box-finished box) launched) (<= remaining 0)) (return))
                 (sb-thread:wait-on-semaphore (%tn-box-sem box) :timeout remaining)))))
      (dotimes (attempt attempts)
        (let ((chosen (%tn-pick pool (* hedge (expt 2 attempt)) tried seqno)))
          (when (null chosen) (return))
          (setf tried (append tried chosen))
          (incf launched (length chosen))
          (dolist (peer chosen)
            (let ((peer peer))
              (sb-thread:make-thread
               (lambda () (%tn-worker pool peer function accept precheck timeout max-answer-size seqno box blame))
               :name "tonnode-query")))
          (wait-until (min overall (+ (%tn-now) stagger)))
          (when (%tn-box-value box) (return-from %tn-call-staggered (values (%tn-box-value box) (%tn-box-peer box))))))
      (wait-until overall))
    (when (%tn-box-value box) (return-from %tn-call-staggered (values (%tn-box-value box) (%tn-box-peer box))))
    (let ((statuses (sb-thread:with-mutex ((%tn-box-lock box)) (copy-list (%tn-box-statuses box)))) (empties (%tn-box-empty box)))
      (if (and empty-ok (plusp empties))
          (values :empty nil)
          (error 'tonnode-error :format-control "no peer gave an acceptable answer to ~A (~D peers, ~D tried: ~D silent, ~D answered wrongly, ~D without the block, ~D empty, ~D unfinished)"
                                :format-arguments (list (tl-obj-name function) (length (tnp-peers pool)) (length tried)
                                                        (+ (count :fail statuses) (count :quiet statuses)) (count :bad statuses) (count :lacks statuses)
                                                        (count :empty statuses) (- (length tried) (length statuses))))))))

(defun tonnode-call (pool function &key (accept #'identity) precheck (timeout 8) (hedge (tnp-hedge pool)) (attempts 4)
                                     (max-answer-size 1048576) seqno empty-ok (blame t) (stagger (tnp-stagger pool)))
  "Run FUNCTION (a tonNode.* object) on the pool.  Each attempt asks fresh peers at once, HEDGE of them in the first and twice as many
in every further attempt (2, 4, 8, 16 with the default: a pool whose peers are mostly silent is searched whole in four attempts);
With STAGGER (seconds; default the pool's, 2.5) the waves overlap instead of following one another (%TN-CALL-STAGGERED); NIL gives the sequence of waves.  With BLAME nil silence is not held against a peer (it is no failure, no cool-down).  ACCEPT gets the answer's octets and returns the value to use (or NIL to reject: (VALUES NIL :EMPTY) means 'answered, nothing there
yet', (VALUES NIL :LACKS) 'answered, does not have it': neither is held against the peer); PRECHECK, given a
peer, returns NIL when the peer does not hold what is asked (cheap query first).  (VALUES VALUE PEER); with EMPTY-OK, :EMPTY when
only empty answers came.  Signals TONNODE-ERROR when no peer gave an acceptable answer."
  (when stagger
    (return-from tonnode-call (%tn-call-staggered pool function accept precheck timeout hedge attempts max-answer-size seqno empty-ok blame stagger)))
  (let ((tried '()) (empties 0) (statuses '()))
    (dotimes (attempt attempts)
      (let ((chosen (%tn-pick pool (* hedge (expt 2 attempt)) tried seqno)))
        (when (null chosen) (return))
        (setf tried (append tried chosen))
        (let ((box (make-%tn-box)) (deadline (+ (%tn-now) timeout 1.5d0)))
          (dolist (peer chosen)
            (let ((peer peer))
              (sb-thread:make-thread
               (lambda () (%tn-worker pool peer function accept precheck timeout max-answer-size seqno box blame))
               :name "tonnode-query")))
          (loop
            (let ((remaining (- deadline (%tn-now))))
              (when (or (%tn-box-value box) (>= (%tn-box-finished box) (length chosen)) (<= remaining 0)) (return))
              (sb-thread:wait-on-semaphore (%tn-box-sem box) :timeout remaining)))
          (when (%tn-box-value box) (return-from tonnode-call (values (%tn-box-value box) (%tn-box-peer box))))
          (incf empties (%tn-box-empty box))
          (setf statuses (append statuses (sb-thread:with-mutex ((%tn-box-lock box)) (copy-list (%tn-box-statuses box))))))))
    (if (and empty-ok (plusp empties))
        (values :empty nil)
        (error 'tonnode-error :format-control "no peer gave an acceptable answer to ~A (~D peers, ~D tried: ~D silent, ~D answered wrongly, ~D without the block, ~D empty, ~D unfinished)"
                              :format-arguments (list (tl-obj-name function) (length (tnp-peers pool)) (length tried)
                                                      (+ (count :fail statuses) (count :quiet statuses)) (count :bad statuses) (count :lacks statuses)
                                                      (count :empty statuses) (- (length tried) (length statuses)))))))

;;; --- what the peers are asked ---------------------------------------------------------------------------------------------------

(defun %boc-answer-p (octets)
  (and (>= (length octets) 4) (= (aref octets 0) #xb5) (= (aref octets 1) #xee) (= (aref octets 2) #x9c) (= (aref octets 3) #x72)))

(defun %answer-object (octets)
  "The TL object of an answer, NIL when it is none (or not decodable)."
  (let ((o (ignore-errors (tl-decode octets)))) (and (tl-obj-p o) o)))

(defun %block-data-of-answer (octets)
  "The block file of a downloadBlock answer: the raw BoC the full nodes send, or the octets of a tonNode.data."
  (cond ((%boc-answer-p octets) (coerce octets '(simple-array (unsigned-byte 8) (*))))
        (t (let ((o (%answer-object octets))) (and o (tl-is o "tonNode.data") (as-octets (tl-get o :data)))))))

(defun %block-data-matches-p (id data)
  "DATA is the file of the block ID: its sha256 is the file hash and the hash of its root cell the root hash."
  (and (equalp (sha256 data) (as-octets (tl-get id :file-hash)))
       (handler-case (equalp (hex->octets (cell-hash-hex (first (parse-boc data)))) (as-octets (tl-get id :root-hash)))
         (error () nil))))

(defun %tn-holds-checker (pool id)
  "A PRECHECK for TONNODE-CALL: does the peer say tonNode.prepared for block ID (a small query over plain ADNL, fast on a miss;
on a :QUIC pool the peer's address is its QUIC endpoint, so the precheck goes over QUIC itself)."
  (lambda (peer)
    (let ((o (%answer-object (overlay-query (tnp-client pool) (tn-peer-host peer) (tn-peer-port peer) (tn-peer-public peer)
                                            (tnp-overlay-id pool) (tl-make "tonNode.prepareBlock" :block id)
                                            :transport (if (eq (tnp-transport pool) :quic) :quic :adnl) :timeout 2))))
      (and o (tl-is o "tonNode.prepared")))))

(defun tonnode-download-block (pool id &key (timeout 30) (prepare t) cache hedge)
  "The file of the block ID (a tonNode.blockIdExt), checked against its file hash and root hash, from the first peer that has it.
With PREPARE (the default) each peer is first asked tonNode.prepareBlock, so that nobody is made to send a file it does not have; without
it the file is asked for at once (one round trip less per block: right for recent blocks nearly every peer has) and a peer that answers
without a block file is 'without the block' (not held against it), one that sends a wrong file is a liar.  CACHE, a hash table from file hash to the file or to a
verified entry (TONNODE-PREFETCH-BLOCKS, the PREFETCHER), is looked at first: an entry is used only when it is the file of ID (checked again here), so a cache
cannot make a wrong block pass; HEDGE overrides the pool's (1 = one peer at a time: no file is sent twice)."
  (let* ((entry (and cache (gethash (as-octets (tl-get id :file-hash)) cache)))
         (hit (if (consp entry) (sixth entry) entry)))
    (when (and hit (%block-data-matches-p id hit)) (return-from tonnode-download-block hit)))
  (values (tonnode-call pool (tl-make "tonNode.downloadBlock" :block id)
                        :accept (lambda (o) (let ((d (%block-data-of-answer o)))
                                              (cond ((null d) (values nil :lacks))
                                                    ((%block-data-matches-p id d) d)
                                                    (t nil))))
                        :precheck (and prepare (%tn-holds-checker pool id)) :timeout timeout :seqno (tl-get id :seqno)
                        :hedge (or hedge (tnp-hedge pool)) :max-answer-size 16777216)))

(defun tonnode-download-block-proof (pool id &key key-block link verify (timeout 30) (prepare t) (attempts 4) (blame t))
  "The BoC of block ID's proof (block_proof#c3), for ID: downloadBlockProof; KEY-BLOCK: downloadKeyBlockProof; with LINK the
proof link.  VERIFY, a function of the proof's octets, is run on every peer's answer: it returns a non-NIL result when the proof
checks out (signatures, see VERIFY-NODE-BLOCK-PROOF) and a peer whose proof does not verify is skipped, so one bad peer cannot
stall the caller.  With PREPARE nil no tonNode.prepareBlock precheck is made (a node that has not got the proof yet says nothing
anyway, and the precheck of a block it holds does not say it holds the proof) and an answer that is no proof is 'without it', not a lie;
ATTEMPTS widen as in TONNODE-CALL.  (VALUES OCTETS VERIFY-RESULT)."
  (let ((v (tonnode-call pool (tl-make (cond ((and key-block link) "tonNode.downloadKeyBlockProofLink")
                                            (key-block "tonNode.downloadKeyBlockProof")
                                            (link "tonNode.downloadBlockProofLink")
                                            (t "tonNode.downloadBlockProof"))
                                      :block id)
                       :accept (lambda (o)
                                 (if (and (not prepare) (not (%boc-answer-p o)))
                                     (values nil :lacks)
                                     (and (%boc-answer-p o)
                                          (handler-case (%same-block-id-p (parse-block-proof (first (parse-boc o))) id)
                                            (error () nil))
                                          (let ((octets (coerce o '(simple-array (unsigned-byte 8) (*)))))
                                            (if verify
                                                (let ((r (handler-case (funcall verify octets) (error () nil)))) (and r (list octets r)))
                                                (list octets nil))))))
                       :precheck (and prepare (%tn-holds-checker pool id)) :timeout timeout :seqno (tl-get id :seqno)
                       :attempts attempts :blame blame :max-answer-size 16777216)))
    (values (first v) (second v))))

(defun tonnode-next-block (pool id)
  "The masterchain block after ID (getNextBlockDescription) as a tonNode.blockIdExt, or :NONE when the peers know none yet.
Only the sequence is checked (the next seqno, the same shard); the block itself is verified when it is downloaded."
  (let ((v (tonnode-call pool (tl-make "tonNode.getNextBlockDescription" :prev-block id)
                         :accept (lambda (o)
                                   (let ((d (%answer-object o)))
                                     (cond ((and d (tl-is d "tonNode.blockDescriptionEmpty")) (values nil :empty))
                                           ((and d (tl-is d "tonNode.blockDescription"))
                                            (let ((n (tl-get d :id)))
                                              (and (= (tl-get n :seqno) (1+ (tl-get id :seqno)))
                                                   (= (tl-get n :workchain) (tl-get id :workchain)) (= (tl-get n :shard) (tl-get id :shard))
                                                   n))))))
                         :timeout 4 :empty-ok t)))
    (if (eq v :empty) :none v)))

(defun tonnode-next-key-block-ids (pool id &key (max-size 8))
  "(VALUES IDS INCOMPLETE): the key blocks after ID that the peers name (getNextKeyBlockIds, at most 8), oldest first; unverified."
  (let ((o (tonnode-call pool (tl-make "tonNode.getNextKeyBlockIds" :block id :max-size max-size)
                         :accept (lambda (o) (let ((d (%answer-object o)))
                                               (cond ((not (and d (tl-is d "tonNode.keyBlocks"))) nil)
                                                     ((tl-get d :error) (values nil :lacks))   ; a node without that part of the chain
                                                     (t d)))))))
    (values (coerce (tl-get o :blocks) 'list) (tl-get o :incomplete))))

(defun tonnode-follow (pool from-id &key (max-steps most-positive-fixnum) on-step)
  "Walk the masterchain forward from FROM-ID one block per query until the peers know no next block (or MAX-STEPS).
(VALUES LAST-ID STEPS).  ON-STEP, when given, is called with each new id and the step count.  The ids are untrusted."
  (let ((id from-id) (steps 0))
    (loop while (< steps max-steps)
          do (let ((next (tonnode-next-block pool id)))
               (when (eq next :none) (return))
               (setf id next) (incf steps)
               (when on-step (funcall on-step id steps))))
    (values id steps)))

(defun tonnode-verified-head (pool from-id key-block &key (max-steps most-positive-fixnum))
  "Follow the chain from FROM-ID to its end, then prove the last block: its proof's signatures must verify against the validator
set of KEY-BLOCK (the masterchain key block cell the caller trusts, the newest one before that block); a peer whose proof does
not verify is skipped.  (VALUES ID INFO STEPS SIGNED-WEIGHT TOTAL-WEIGHT SIGNATURES): INFO the block header (gen_utime tells how
fresh it is)."
  (multiple-value-bind (id steps) (tonnode-follow pool from-id :max-steps max-steps)
    (multiple-value-bind (octets result)
        (tonnode-download-block-proof pool id :verify (lambda (o) (multiple-value-list (verify-node-block-proof-by-key-block o id key-block))))
      (declare (ignore octets))
      (destructuring-bind (info weight total count) result
        (values id info steps weight total count)))))

(defun tonnode-advance-key-block (pool key-block-id key-block)
  "The key block after KEY-BLOCK-ID (its cell KEY-BLOCK is trusted), downloaded and verified: file hash and root hash from its id,
and its proof signed by the validator set KEY-BLOCK names (a peer whose proof does not verify is skipped).
(VALUES NEXT-ID NEXT-CELL NEXT-OCTETS), NIL when the peers name no later key block, TONNODE-ERROR when what they serve does not
verify."
  (let ((ids (tonnode-next-key-block-ids pool key-block-id)))
    (when ids
      (let* ((next (first ids))
             (config-root (key-block-config-root key-block))
             (vset (first (key-block-validator-sets config-root))))
        (tonnode-download-block-proof
         pool next :key-block t
                   :verify (lambda (o)
                             (let ((info (verify-node-block-proof o next vset config-root)))
                               (and (getf info :key-block) info))))
        (let ((octets (tonnode-download-block pool next)))
          (values next (first (parse-boc octets)) octets))))))

;;; --- peers from the DHT, verified blocks, the shards of a masterchain block ----------------------------------------------------------

(defun dht-overlay-peers (dht overlay-id &key (max 16) (want 40))
  "Peers for MAKE-TONNODE-POOL from the public overlay OVERLAY-ID: the verified members the DHT knows (DHT-FIND-OVERLAY-MEMBERS, WANT
of them at most), each resolved through its signed address list (DHT-FIND-ADDRESS) to an IPv4 UDP endpoint; at most MAX peers.
(VALUES PEERS MEMBERS NOTES), PEERS a list of (HOST PORT PUBLIC-KEY), MEMBERS the number of verified members found, NOTES the short
strings telling what each DHT node asked said (DHT-FIND-OVERLAY-MEMBERS): read them when no member is found."
  (multiple-value-bind (members notes) (dht-find-overlay-members dht overlay-id :want want)
   (let ((peers '()) (n 0))
    (loop for (public . nil) in members
          while (< n max)
          do (let ((address (ignore-errors (dht-find-address dht (adnl-short-id public)))))
               (when address
                 (multiple-value-bind (strings quic-host quic-port host port) (adnl-address-summary address)
                   (declare (ignore strings quic-host quic-port))
                   (when (and host port)
                     (incf n)
                     (push (list host port public) peers))))))
    (values (nreverse peers) (length members) notes))))

(defun shard-descr-block-id (descr)
  "The tonNode.blockIdExt of the block a shard description (a plist of BLOCK-SHARD-DESCRIPTIONS) names."
  (tl-make "tonNode.blockIdExt" :workchain (getf descr :workchain) :shard (%signed64 (getf descr :shard)) :seqno (getf descr :seqno)
                                :root-hash (getf descr :root-hash) :file-hash (getf descr :file-hash)))

(defun tonnode-verified-block (pool id &key (timeout 30) (prepare t) cache)
  "The block ID (a tonNode.blockIdExt whose hashes the caller trusts), downloaded from the first peer of POOL that has it and read:
the file hash and the root hash are the id's (VERIFY-BLOCK-DATA), BlockInfo agrees with the id, and the state_update is a Merkle
update.  (VALUES BLOCK INFO NEW-STATE-HASH OLD-STATE-HASH OCTETS): the root cell, the parsed BlockInfo, the hash the state has after
the block and before it.  A block whose data does not verify signals a PROOF-ERROR."
  (let ((entry (and cache (gethash (as-octets (tl-get id :file-hash)) cache))))
    (when (and (consp entry) (%same-block-id-p id (first entry)))      ; read and checked by a prefetch worker for this very id
      (return-from tonnode-verified-block (values-list (rest entry)))))
  (let* ((octets (tonnode-download-block pool id :timeout timeout :prepare prepare :cache cache))
         (checked (verify-block-data (tl-make "liteServer.blockData" :id id :data octets) id))
         (block (getf checked :block))
         (update (svref (cell-refs block) 2)))
    (unless (eql 4 (cell-special-type update))
      (error 'tonnode-error :format-control "block ~D: the state_update is not a Merkle update" :format-arguments (list (tl-get id :seqno))))
    (multiple-value-bind (old new) (merkle-update-hashes update)
      (values block (getf checked :info) new old octets))))

(defun tonnode-verified-masterchain-block (pool id key-block &key (timeout 30) (rounds 3) (round-pause 1.5))
  "The masterchain block ID, proven and read: its proof must be signed by the validator set of KEY-BLOCK (the masterchain key block
cell the caller trusts, the newest one before ID; a peer whose proof does not verify is skipped), and the block data must be the
file the id names.  The id of a block that is only seconds old may come from a supplier that is ahead of the peers (a node without the
proof answers nothing): the proof is asked for in up to ROUNDS rounds (no prepareBlock precheck, TIMEOUT at most 6 s, two attempts
each), ROUND-PAUSE seconds apart, before TONNODE-ERROR is signalled.  (VALUES BLOCK INFO NEW-STATE-HASH SHARDS SIGNED-WEIGHT TOTAL-WEIGHT): SHARDS the shard descriptions the block
commits to (BLOCK-SHARD-DESCRIPTIONS), each one the id of a shard block that is thereby trusted."
  (multiple-value-bind (proof result)
      (let ((error nil))
        (dotimes (round rounds (error error))
          (handler-case
              (return (tonnode-download-block-proof pool id :timeout (min timeout 6) :prepare nil :attempts 2 :blame nil
                                                            :verify (lambda (o) (multiple-value-list (verify-node-block-proof-by-key-block o id key-block)))))
            (tonnode-error (e) (setf error e) (when (< (1+ round) rounds) (sleep round-pause))))))
    (declare (ignore proof))
    (destructuring-bind (proof-info weight total count) result
      (declare (ignore proof-info count))
      (multiple-value-bind (block info new-state-hash) (tonnode-verified-block pool id :timeout timeout)
        (values block info new-state-hash (block-shard-descriptions block) weight total)))))


;;; --- the state roots at a masterchain block --------------------------------------------------------------------------------------------

(defun tonnode-shard-states (pool shards &key (workchain 0) (timeout 30))
  "The blocks of the shards SHARDS (descriptions from BLOCK-SHARD-DESCRIPTIONS of a trusted masterchain block) that belong to
WORKCHAIN, each downloaded from POOL (a pool over that shard's overlay) and read (TONNODE-VERIFIED-BLOCK); its header must also
agree with the description (the logical times).  (VALUES STATES): a list of plists (:DESCR :ID :INFO :STATE-HASH :OLD-STATE-HASH),
STATE-HASH the hash the shard state has after the block.  A block that does not match its description signals a PROOF-ERROR."
  (loop for descr in shards
        when (= workchain (getf descr :workchain))
          collect (let ((id (shard-descr-block-id descr)))
                    (multiple-value-bind (block info new old) (tonnode-verified-block pool id :timeout timeout)
                      (declare (ignore block))
                      (unless (and (= (getf info :start-lt) (getf descr :start-lt)) (= (getf info :end-lt) (getf descr :end-lt)))
                        (error 'proof-error :format-control "shard block ~D: its logical times differ from its description in the masterchain block"
                                            :format-arguments (list (getf descr :seqno))))
                      (list :descr descr :id id :info info :state-hash new :old-state-hash old)))))

(defun tonnode-head-state (mc-pool shard-pool mc-id key-block &key (workchain 0) (timeout 30))
  "The trusted state roots at the masterchain block MC-ID: the block is proven by the validator set of KEY-BLOCK (the masterchain key
block cell the caller trusts, the newest one before MC-ID) and read (TONNODE-VERIFIED-MASTERCHAIN-BLOCK); the shards of WORKCHAIN it
commits to are then fetched from SHARD-POOL (a pool over the overlay of the workchain's shards) and each verified against its
description.  (VALUES MC-STATE SHARD-STATES SIGNED-WEIGHT TOTAL-WEIGHT): MC-STATE = plist (:ID :INFO :STATE-HASH), SHARD-STATES as in
TONNODE-SHARD-STATES.  Every hash returned is bound to the signed masterchain block: an account proof against one of these state
hashes is a proof against the chain."
  (multiple-value-bind (block info state-hash shards weight total) (tonnode-verified-masterchain-block mc-pool mc-id key-block :timeout timeout)
    (declare (ignore block))
    (values (list :id mc-id :info info :state-hash state-hash)
            (tonnode-shard-states shard-pool shards :workchain workchain :timeout timeout)
            weight total)))

;;; --- following a shard: the blocks between the last one seen and the newest one ----------------------------------------------------------

(defun tonnode-chain-consistent-p (blocks)
  "True when BLOCKS (plists of TONNODE-SHARD-CHAIN, oldest first) hang together in their state hashes: a block with one predecessor
that is not a split starts from the state the predecessor ended in.  Predecessors outside BLOCKS are not checked here (the caller
compares the oldest block's :OLD-STATE-HASH with the state it holds), and merges and splits change the state's shape: not checked."
  (every (lambda (b)
           (let ((prev (getf b :prev)))
             (or (/= 1 (length prev)) (getf b :after-split)
                 (let ((p (find (shard-descr-block-id (first prev)) blocks :key (lambda (x) (getf x :id)) :test #'%same-block-id-p)))
                   (or (null p) (equalp (getf b :old-state-hash) (getf p :state-hash)))))))
         blocks))

(defun tonnode-shard-chain (pool tip known &key (max-blocks 32) (timeout 30) cache)
  "The blocks of a shard from just after KNOWN up to TIP, oldest first, each downloaded from POOL and verified by its hashes
(TONNODE-VERIFIED-BLOCK), found by walking the predecessor references inside the blocks (PARSE-BLOCK-LINKS) back from TIP, so that
no block between can be left out or invented: a block is only fetched when a block already verified names it.  TIP is a
tonNode.blockIdExt the caller trusts (a shard description of a signed masterchain block), KNOWN a list of block ids the caller
already trusts (the walk stops at them, and does not fetch them).  A list of plists (:ID :INFO :STATE-HASH :OLD-STATE-HASH :PREV
:MC-REF :AFTER-SPLIT :BLOCK), by seqno (a descendant always has a bigger seqno than its ancestors).  More than MAX-BLOCKS to fetch,
or a block no peer has, signals a TONNODE-ERROR: the caller should then start from a newer trusted block; the state hashes of the
blocks that hang together are checked (TONNODE-CHAIN-CONSISTENT-P), a break signals a PROOF-ERROR.  CACHE (see
TONNODE-DOWNLOAD-BLOCK) only saves the downloads: the walk and every check are the same."
  (let ((known (if (and known (not (consp known))) (list known) known))
        (seen '()) (pending (list tip)) (result '()))
    (loop while pending
          do (let ((id (pop pending)))
               (unless (or (member id known :test #'%same-block-id-p) (member id seen :test #'%same-block-id-p))
                 (when (>= (length result) max-blocks)
                   (error 'tonnode-error :format-control "more than ~D blocks between the last known block and ~D" :format-arguments (list max-blocks (tl-get tip :seqno))))
                 (push id seen)
                 (multiple-value-bind (block info new old) (tonnode-verified-block pool id :timeout timeout :prepare nil :cache cache)
                   (multiple-value-bind (prev mc-ref after-split) (parse-block-links block id)
                     (push (list :id id :info info :state-hash new :old-state-hash old :prev prev :mc-ref mc-ref
                                 :after-split (and after-split t) :block block)
                           result)
                     (dolist (p prev) (push (shard-descr-block-id p) pending)))))))
    (let ((blocks (sort result #'< :key (lambda (r) (getf (getf r :info) :seqno)))))
      (unless (tonnode-chain-consistent-p blocks)
        (error 'proof-error :format-control "the state hashes of the blocks of ~D back do not hang together" :format-arguments (list (tl-get tip :seqno))))
      blocks)))

(defun tonnode-follow-shard (pool tip last &key (max-blocks 32) (timeout 30) cache)
  "The blocks of a shard after LAST, up to TIP (a trusted block id): LAST is a plist (:ID block id :STATE-HASH the hash of the state
after it) of the newest block already processed.  TONNODE-SHARD-CHAIN, and the oldest block must start from the state LAST ended in
(a PROOF-ERROR when it does not: nothing returned is then to be believed)."
  (let ((blocks (tonnode-shard-chain pool tip (getf last :id) :max-blocks max-blocks :timeout timeout :cache cache)))
    (let ((first-block (first blocks)))
      (when (and first-block (= 1 (length (getf first-block :prev))) (not (getf first-block :after-split))
                 (%same-block-id-p (shard-descr-block-id (first (getf first-block :prev))) (getf last :id))
                 (not (equalp (getf first-block :old-state-hash) (getf last :state-hash))))
        (error 'proof-error :format-control "block ~D does not start from the state the last known block ended in"
                            :format-arguments (list (getf (getf first-block :info) :seqno)))))
    blocks))

;;; --- the follower: the trusted heads of the masterchain and of the basechain shards, advancing -------------------------------------------

;;; --- catching up: shard block ids from masterchain blocks, the blocks downloaded in parallel ---------------------------------------------
;;;
;;; The walk of TONNODE-SHARD-CHAIN fetches one block after the other (a block names only its predecessor): at the speed of the
;;; chain (about 2.5 blocks a second) a follower cannot gain on it.  But every masterchain block names the newest basechain shard
;;; block, nearly one for each, and the nodes send up to 10 successive masterchain blocks in one answer (downloadNextBlocksFull,
;;; LZ4 compressed): so the ids of the blocks between are known cheaply and the blocks can be fetched side by side.  Nothing here
;;; is trusted: the ids are HINTS, the blocks land in a cache, and the walk of TONNODE-SHARD-CHAIN, which checks every block against
;;; the ids a trusted block names, takes its blocks from the cache instead of the network.  A wrong hint costs a download, nothing else.

(defun lz4-decompress (octets &key (max-size 16777216))
  "The LZ4 block OCTETS (the raw block format the nodes use for compressed block files: no frame, no size) decompressed, at most
MAX-SIZE octets.  Truncated or inconsistent input, or more than MAX-SIZE octets of output, signals a TONNODE-ERROR."
  (%lz4-decompress (if (typep octets '(simple-array (unsigned-byte 8) (*))) octets (coerce octets '(simple-array (unsigned-byte 8) (*))))
                   max-size))

(defun %lz4-decompress (octets max-size)
  (declare (type (simple-array (unsigned-byte 8) (*)) octets) (type fixnum max-size) (optimize (speed 3) (safety 1)))
  (progn
    (let* ((n (length octets)) (cap (min max-size (max 1024 (* 4 n))))
           (out (make-array cap :element-type '(unsigned-byte 8))) (ip 0) (op 0))
      (declare (type fixnum n cap ip op) (type (simple-array (unsigned-byte 8) (*)) out))
      (flet ((fail (what) (error 'tonnode-error :format-control "lz4: ~A" :format-arguments (list what)))
             (grow (need)
               (declare (type fixnum need))
               (when (> need max-size) (error 'tonnode-error :format-control "lz4: more than ~D octets of output" :format-arguments (list max-size)))
               (when (> need cap)
                 (let* ((new-cap (min max-size (max need (* 2 cap)))) (new (make-array new-cap :element-type '(unsigned-byte 8))))
                   (declare (type fixnum new-cap))
                   (replace new out :end2 op)
                   (setf out new cap new-cap)))))
        (loop while (< ip n)
              do (let* ((token (aref octets ip)) (lit (ash token -4)))
                   (declare (type fixnum token lit))
                   (incf ip)
                   (when (= lit 15)
                     (loop (when (>= ip n) (fail "truncated literal length"))
                           (let ((b (aref octets ip))) (incf ip) (incf lit b) (when (< b 255) (return)))
                           (when (> lit max-size) (fail "literal run too long"))))
                   (when (> (+ ip lit) n) (fail "the literals run past the input"))
                   (grow (+ op lit))
                   (replace out octets :start1 op :start2 ip :end2 (+ ip lit))
                   (incf op lit) (incf ip lit)
                   (when (>= ip n) (return))                    ; the last sequence has literals only
                   (when (> (+ ip 2) n) (fail "truncated match offset"))
                   (let ((offset (logior (aref octets ip) (ash (aref octets (1+ ip)) 8))) (ml (logand token 15)))
                     (declare (type fixnum offset ml))
                     (incf ip 2)
                     (when (or (zerop offset) (> offset op)) (fail "match offset out of range"))
                     (when (= ml 15)
                       (loop (when (>= ip n) (fail "truncated match length"))
                             (let ((b (aref octets ip))) (incf ip) (incf ml b) (when (< b 255) (return)))
                             (when (> ml max-size) (fail "match too long"))))
                     (incf ml 4)
                     (grow (+ op ml))
                     (let ((src (- op offset)))
                       (declare (type fixnum src))
                       (dotimes (i ml) (setf (aref out op) (aref out src)) (incf op) (incf src))))))
        (subseq out 0 op)))))

(defun %data-full-block (d)
  "(VALUES ID BLOCK-CELL PROOF-CELL) of a tonNode.DataFull (plain, or LZ4 compressed with the proof and the block as two roots); NIL
for any other kind or one that does not decode.  PROOF-CELL, the root of the block proof the node holds, is NIL when there is none."
  (handler-case
      (cond ((tl-is d "tonNode.dataFull")
             (values (tl-get d :id) (first (parse-boc (as-octets (tl-get d :block))))
                     (ignore-errors (first (parse-boc (as-octets (tl-get d :proof)))))))
            ((tl-is d "tonNode.dataFullCompressed")
             (let ((roots (parse-boc (lz4-decompress (as-octets (tl-get d :compressed)) :max-size 16777216))))
               (and (= 2 (length roots)) (values (tl-get d :id) (second roots) (first roots)))))
            (t nil))
    (error () nil)))

(defun tonnode-next-masterchain-blocks (pool prev-id &key (max-blocks 10) (timeout 12) (hedge 1) (attempts 4))
  "The masterchain blocks after PREV-ID, up to MAX-BLOCKS (at most 10), one downloadNextBlocksFull from one peer at a time (HEDGE 1: no
answer is sent twice): a list of plists (:ID the id the peer names :BLOCK the root cell :PROOF the root cell of its block proof, or
NIL), oldest first, each the next seqno after
the one before, and its root hash the cell's: the blocks are NOT proven (a block whose proof the peer holds is all it sends).
NIL when no peer has a newer block: the search widens (HEDGE, then twice as many peers in each of ATTEMPTS attempts: 1+2+4+8 peers
with the default), because the peers differ in how far they are (field report 2026-11-14: peers that answer at once with nothing
newer, for minutes, while others have the blocks)."
  (let ((v (tonnode-call pool (tl-make "tonNode.downloadNextBlocksFull" :prev-block prev-id :max-blocks max-blocks)
                         :accept (lambda (o)
                                   (let ((d (%answer-object o)) (out '()) (expect (1+ (tl-get prev-id :seqno))))
                                     (and d (tl-is d "tonNode.nextBlocksFull")
                                          (progn
                                            (dolist (x (coerce (tl-get d :blocks) 'list))
                                              (multiple-value-bind (id cell proof) (%data-full-block x)
                                                (if (and id cell (= (tl-get id :workchain) -1) (= (tl-get id :seqno) expect)
                                                         (equalp (hex->octets (cell-hash-hex cell)) (as-octets (tl-get id :root-hash))))
                                                    (progn (push (list :id id :block cell :proof proof) out) (incf expect))
                                                    (return))))
                                            (if out (nreverse out) (values nil :empty))))))
                         :timeout timeout :hedge hedge :attempts attempts :empty-ok t :max-answer-size 2097152)))
    (if (eq v :empty) nil v)))

(defun tonnode-next-masterchain-block (pool prev-id &key (timeout 8) (hedge 2) (attempts 2))
  "The ONE masterchain block after PREV-ID, block and proof, by tonNode.downloadNextBlockFull (what nodes before protocol 3.2 use, and
the way when downloadNextBlocksFull gives nothing: field report 2026-11-14, five peers named the next block and gave none).  A list
of one plist as TONNODE-NEXT-MASTERCHAIN-BLOCKS gives, NIL when no peer has one."
  (let ((v (tonnode-call pool (tl-make "tonNode.downloadNextBlockFull" :prev-block prev-id)
                         :accept (lambda (o)
                                   (let ((d (%answer-object o)))
                                     (multiple-value-bind (id cell proof) (and d (%data-full-block d))
                                       (if (and id cell (= (tl-get id :workchain) -1) (= (tl-get id :seqno) (1+ (tl-get prev-id :seqno)))
                                                (equalp (hex->octets (cell-hash-hex cell)) (as-octets (tl-get id :root-hash))))
                                           (list (list :id id :block cell :proof proof))
                                           (values nil :empty)))))
                         :timeout timeout :hedge hedge :attempts attempts :empty-ok t :max-answer-size 2097152)))
    (if (eq v :empty) nil v)))

(defun tonnode-masterchain-range (pool from-id to-seqno &key (max-blocks 400) (timeout 12) (deadline 60) on-block)
  "The masterchain blocks after FROM-ID up to the seqno TO-SEQNO (NIL: as far as the peers have them, MAX-BLOCKS at most), oldest
first: fewer when the peers stop giving blocks (an error of a query ends the range, it is not signalled).  Batches of up to 10
(TONNODE-NEXT-MASTERCHAIN-BLOCKS; the first asks two peers at once, six in all, with a short timeout: an answer with nothing is
common near the head and the peers differ in how far they are; the next ones one at a time, a batch can be 400 KB); when the first
batch gives nothing the blocks are asked for one by one (TONNODE-NEXT-MASTERCHAIN-BLOCK) from then on.  No new query is begun after
DEADLINE seconds.  ON-BLOCK, a function, is called with each block as soon as it is read (an error in it is ignored): the blocks
are worked on while the next ones are fetched.  (VALUES BLOCKS QUERIES), QUERIES a list of (SECONDS BLOCKS-GIVEN KIND) per query made, KIND :BATCH or :SINGLE;
the last one gave none when the peers had no more."
  (let ((prev from-id) (result '()) (count 0) (queries '()) (single nil) (start (%tn-now)) (to-seqno (or to-seqno most-positive-fixnum)))
    (loop while (and (< (tl-get prev :seqno) to-seqno) (< count max-blocks) (< (- (%tn-now) start) deadline))
          do (let* ((t0 (%tn-now))
                    (batch (handler-case
                               (if single
                                   (tonnode-next-masterchain-block pool prev :timeout (min timeout 8))
                                   (tonnode-next-masterchain-blocks pool prev :max-blocks (min 10 (- to-seqno (tl-get prev :seqno)))
                                                                              :timeout (if result timeout (min timeout 6)) :hedge (if result 1 2) :attempts (if result 3 2)))
                             (tonnode-error () nil))))
               (push (list (- (%tn-now) t0) (length batch) (if single :single :batch)) queries)
               (when (and (null batch) (null result) (not single))
                 (setf single t)
                 (let ((t1 (%tn-now)))
                   (setf batch (handler-case (tonnode-next-masterchain-block pool prev :timeout (min timeout 8)) (tonnode-error () nil)))
                   (push (list (- (%tn-now) t1) (length batch) :single) queries)))
               (when (null batch) (return))
               (dolist (b batch) (push b result) (incf count) (when on-block (ignore-errors (funcall on-block b))))
               (setf prev (getf (first result) :id))))
    (values (nreverse result) (nreverse queries))))

(defun %hint-shard-ids (mc-blocks workchain)
  "The ids of the WORKCHAIN shard blocks that the masterchain blocks MC-BLOCKS (plists with :BLOCK, as TONNODE-NEXT-MASTERCHAIN-BLOCKS
gives them) name, oldest first, each once.  Hints only."
  (let ((seen (make-hash-table :test 'equalp)) (ids '()))
    (dolist (b mc-blocks)
      (dolist (descr (ignore-errors (block-shard-descriptions (getf b :block))))
        (when (= (getf descr :workchain) workchain)
          (let* ((id (shard-descr-block-id descr)) (key (as-octets (tl-get id :file-hash))))
            (unless (gethash key seen) (setf (gethash key seen) t) (push id ids))))))
    (nreverse ids)))

(defstruct (prefetcher (:conc-name pf-))
  "Worker threads that download and read blocks while ids are still being added (TONNODE-START-PREFETCHER)."
  pool cache (lock (sb-thread:make-mutex :name "prefetcher")) (queue '()) (done nil) (stop nil) (threads '()) (seen (make-hash-table :test 'equalp))
  (bytes 0) (failed 0) (added 0) (start 0d0) (deadline 120))

(defun tonnode-start-prefetcher (pool &key (parallel 6) (timeout 15) (deadline 120) cache)
  "A PREFETCHER: PARALLEL threads that take block ids from a queue (PREFETCHER-ADD), download each block from one peer at a time (no
file is sent twice), read it (TONNODE-VERIFIED-BLOCK: the hashes of the id, the header, the Merkle update: the CPU work is done in the
threads, side by side) and keep the result in the cache (a hash table from file hash to the entry (ID BLOCK INFO NEW-STATE-HASH
OLD-STATE-HASH OCTETS); TONNODE-VERIFIED-BLOCK and TONNODE-DOWNLOAD-BLOCK take from it, after checking it is the block of the id they are
asked for).  No new download is begun after DEADLINE seconds from the start; a block that cannot be had is counted as failed, no error."
  (let ((pf (make-prefetcher :pool pool :cache (or cache (make-hash-table :test 'equalp :synchronized t)) :start (%tn-now) :deadline deadline)))
    (flet ((worker ()
             (loop
               (when (or (pf-stop pf) (> (- (%tn-now) (pf-start pf)) (pf-deadline pf))) (return))
               (let ((id (sb-thread:with-mutex ((pf-lock pf)) (pop (pf-queue pf)))))
                 (cond
                   (id (handler-case
                           (multiple-value-bind (block info new old octets) (tonnode-verified-block pool id :timeout timeout :prepare nil)
                             (setf (gethash (as-octets (tl-get id :file-hash)) (pf-cache pf)) (list id block info new old octets))
                             (sb-thread:with-mutex ((pf-lock pf)) (incf (pf-bytes pf) (length octets))))
                         (error () (sb-thread:with-mutex ((pf-lock pf)) (incf (pf-failed pf))))))
                   ((pf-done pf) (return))
                   (t (sleep 0.02)))))))
      (setf (pf-threads pf) (loop repeat (max 1 parallel) collect (sb-thread:make-thread #'worker :name "tonnode-prefetch"))))
    pf))

(defun prefetcher-add (pf ids)
  "Queue the block ids IDS (tonNode.blockIdExt hints) for the workers; an id seen before, or already in the cache, is left out."
  (sb-thread:with-mutex ((pf-lock pf))
    (dolist (id ids)
      (let ((key (as-octets (tl-get id :file-hash))))
        (unless (or (gethash key (pf-seen pf)) (gethash key (pf-cache pf)))
          (setf (gethash key (pf-seen pf)) t)
          (incf (pf-added pf))
          (setf (pf-queue pf) (nconc (pf-queue pf) (list id)))))))
  nil)

(defun prefetcher-finish (pf &key abort)
  "Let the workers finish the queue (ABORT: stop them at once) and wait for them.  (VALUES CACHE STATS), STATS a plist (:IDS ids queued
:FETCHED entries in the cache :FAILED :BYTES :SECONDS)."
  (setf (pf-done pf) t)
  (when abort (setf (pf-stop pf) t))
  (dolist (th (pf-threads pf)) (sb-thread:join-thread th :default nil))
  (values (pf-cache pf)
          (list :ids (pf-added pf) :fetched (hash-table-count (pf-cache pf)) :failed (pf-failed pf) :bytes (pf-bytes pf) :seconds (- (%tn-now) (pf-start pf)))))

(defun tonnode-prefetch-blocks (pool ids &key (parallel 6) (timeout 15) (deadline 45) cache)
  "Download and read the blocks IDS (hints) side by side: a PREFETCHER that is given them all at once and finished.  (VALUES CACHE STATS)."
  (let ((pf (tonnode-start-prefetcher pool :parallel (max 1 (min parallel (length ids))) :timeout timeout :deadline deadline :cache cache)))
    (prefetcher-add pf ids)
    (prefetcher-finish pf)))

(defun tonnode-send-external-message (pool message-boc &key (count 4) (repeat 2) keypair)
  "Inject the external inbound message MESSAGE-BOC (octets) into the chain: broadcast it in the public shard overlay of POOL to COUNT of
its members (best ranked first: answering peers, then unknown ones), REPEAT times each (UDP loses datagrams), as a tonNode.
externalMessageBroadcast signed by KEYPAIR (default a fresh key: the sender needs no membership).  Every member judges the message
for itself (a node may have ext_messages_broadcast_disabled_), so several are asked; a member that accepts passes it to the
collators.  Nothing comes back: whether it was included is seen in the account (a block's account changes, or a cold read of its last
transaction).  The POOL must be the pool of the overlay of the shard that holds the destination account (the masterchain pool for
a masterchain account).  Returns the list of (HOST . PORT) it was sent to.  Gate 5: accepted by a node 2026.10 from a non-member."
  (let* ((node (ocl-node (tnp-client pool)))
         (keypair (or keypair (adnl-generate-keypair)))
         (data (external-message-broadcast-octets message-boc))
         (peers (%tn-pick pool count '() nil)))
    (dolist (p peers)
      (dotimes (i repeat)
        (overlay-send-broadcast node (tn-peer-host p) (tn-peer-port p) (tn-peer-public p) (tnp-overlay-id pool) keypair data)))
    (mapcar (lambda (p) (cons (tn-peer-host p) (tn-peer-port p))) peers)))

(defstruct (tonnode-follower (:conc-name tfollower-))
  "What a client that follows the chain keeps: KEY-BLOCK the masterchain key block cell whose validator set signs what comes next,
MC-ID the newest masterchain block taken in, SHARDS the basechain shard tips taken in: a list of plists (:ID tonNode.blockIdExt
:STATE-HASH the hash of the shard state after that block), KEY-ID the id of KEY-BLOCK (kept with it: a pinned old key block is
served by fewer and fewer nodes, the newest one proven is the place to resume from), STATE-FILE where SHARDS, MC-ID and the key
block (a second file, STATE-FILE.key.boc) are kept (or NIL).  RANGE-FAILED-AT (not kept): when the nodes last gave no masterchain
blocks after MC-ID (monotonic seconds): the steps do not ask again for a minute."
  key-block key-id mc-id (shards '()) state-file (range-failed-at -1d6))

(defvar *tonnode-prefetch-stats* nil
  "What the last catch-up of TONNODE-FOLLOWER-STEP or -ADVANCE did: a plist (:MC-BLOCKS masterchain blocks read :MC-SECONDS :BATCHES
((seconds blocks kind) per masterchain query, ADVANCE only) :IDS :FETCHED :FAILED :BYTES :SECONDS of the shard block downloads), NIL when it made none.
For a report.")

(defun %follower-prefetch (follower mc-pool shard-pool mc-id shards workchain parallel timeout)
  "A cache for the walk of a step that has some distance to cover: the shard blocks the masterchain blocks between the follower's
masterchain block and MC-ID name (and the tips SHARDS of MC-ID itself), fetched side by side.  NIL for a short distance."
  (let ((old (tfollower-mc-id follower)))
    (setf *tonnode-prefetch-stats* nil)
    (when (and old (tfollower-shards follower) (< 3 (- (tl-get mc-id :seqno) (tl-get old :seqno)) 400)
               (> (- (%tn-now) (tfollower-range-failed-at follower)) 60))
      (let* ((t0 (%tn-now))
             (pf (tonnode-start-prefetcher shard-pool :parallel parallel :timeout (min timeout 15) :deadline 90))
             (ok nil))
        (unwind-protect
             (let* ((mc-blocks (tonnode-masterchain-range mc-pool old (1- (tl-get mc-id :seqno)) :timeout (min timeout 12) :deadline 20
                                                          :on-block (lambda (b) (prefetcher-add pf (%hint-shard-ids (list b) workchain)))))
                    (t1 (%tn-now)))
               (prefetcher-add pf (loop for d in shards when (= workchain (getf d :workchain)) collect (shard-descr-block-id d)))
               (multiple-value-bind (cache stats) (prefetcher-finish pf)
                 (setf ok t)
                 (when (null mc-blocks) (setf (tfollower-range-failed-at follower) (%tn-now)))
                 (setf *tonnode-prefetch-stats* (list* :mc-blocks (length mc-blocks) :mc-seconds (- t1 t0) stats))
                 cache))
          (unless ok (prefetcher-finish pf :abort t)))))))

(defun %follower-start-consistent-p (blocks table)
  "True when every block of BLOCKS with exactly one predecessor, a tip of TABLE, that is not a split starts from the state hash the
table holds for it.  Blocks reached through merges and splits are not compared here: their state changes shape."
  (every (lambda (b)
           (let ((prev (getf b :prev)))
             (or (/= 1 (length prev)) (getf b :after-split)
                 (let ((entry (find (shard-descr-block-id (first prev)) table :key (lambda (e) (getf e :id)) :test #'%same-block-id-p)))
                   (or (null entry) (equalp (getf b :old-state-hash) (getf entry :state-hash)))))))
         blocks))

(defun %follower-gap (table tip)
  "How many blocks TIP is ahead of the tip of TABLE that is the same shard (NIL when the table holds no block of that shard)."
  (let ((held (find-if (lambda (e) (let ((id (getf e :id)))
                                     (and (= (tl-get id :workchain) (tl-get tip :workchain)) (= (tl-get id :shard) (tl-get tip :shard)))))
                       table)))
    (and held (- (tl-get tip :seqno) (tl-get (getf held :id) :seqno)))))

(defun tonnode-follower-apply (follower shard-pool shards &key (workchain 0) (max-blocks 32) (timeout 30) cache)
  "Take in SHARDS, the shard descriptions of a trusted masterchain block (BLOCK-SHARD-DESCRIPTIONS), for WORKCHAIN: a shard tip the
follower already holds stays; a new tip is walked back, through POOL, to the tips held (TONNODE-SHARD-CHAIN: splits and merges end
at the parents), and the first look at a shard (nothing held yet) takes only its tip block.  The state hashes must hang together
(PROOF-ERROR otherwise: nothing is changed then).  A tip more than MAX-BLOCKS ahead of the held tip of the same shard (the follower
was away: the chain makes about 2.4 blocks a second) is NOT walked: the follower starts afresh from that tip, as at the first look,
and says so.  (VALUES NEW-BLOCKS RESYNCED): the blocks fetched, plists of TONNODE-SHARD-CHAIN, oldest first within a shard: each of
them can be read with BLOCK-ACCOUNT-CHANGES; RESYNCED a list of plists (:ID the new tip, :SKIPPED how many blocks were not looked at):
what those blocks changed has not been seen, an account has to be read again (a proof against the new state hash)."
  (let* ((table (tfollower-shards follower))
         (known (mapcar (lambda (e) (getf e :id)) table))
         (new-table '()) (new-blocks '()) (resynced '()))
    (dolist (descr (remove-if-not (lambda (d) (= workchain (getf d :workchain))) shards))
      (let* ((tip (shard-descr-block-id descr))
             (entry (find tip table :key (lambda (e) (getf e :id)) :test #'%same-block-id-p))
             (gap (and (not entry) (%follower-gap table tip))))
        (cond
          (entry (push entry new-table))
          ((and gap (> gap max-blocks))
           (let ((state (first (tonnode-shard-states shard-pool (list descr) :workchain workchain :timeout timeout))))
             (push (list :id tip :state-hash (getf state :state-hash)) new-table)
             (push (list :id tip :skipped gap) resynced)))
          (table
           (let ((blocks (tonnode-shard-chain shard-pool tip known :max-blocks max-blocks :timeout timeout :cache cache)))
             (unless (%follower-start-consistent-p blocks table)
               (error 'proof-error :format-control "the blocks up to ~D of shard ~16,'0X do not start from the states held"
                                   :format-arguments (list (getf descr :seqno) (getf descr :shard))))
             (setf new-blocks (append new-blocks blocks))
             (push (list :id tip :state-hash (getf (car (last blocks)) :state-hash)) new-table)))
          (t
           (let ((state (first (tonnode-shard-states shard-pool (list descr) :workchain workchain :timeout timeout))))
             (push (list :id tip :state-hash (getf state :state-hash)) new-table))))))
    (setf (tfollower-shards follower) (nreverse new-table))
    (values new-blocks (nreverse resynced))))

(defun tonnode-follower-save (follower &optional (path (tfollower-state-file follower)))
  "Write the shard tips and the masterchain block of FOLLOWER to PATH (hashes in hex, a readable list, replaced atomically)."
  (when path
    (flet ((id-plist (id) (list :workchain (tl-get id :workchain) :shard (tl-get id :shard) :seqno (tl-get id :seqno)
                                :root-hash (octets->hex (as-octets (tl-get id :root-hash))) :file-hash (octets->hex (as-octets (tl-get id :file-hash))))))
      (let ((tmp (format nil "~A.tmp" path)))
        (with-open-file (f tmp :direction :output :if-exists :supersede :external-format :utf-8)
          (let ((*print-readably* nil) (*print-pretty* nil))
            (prin1 (list :follower 1
                         :mc-id (and (tfollower-mc-id follower) (id-plist (tfollower-mc-id follower)))
                         :key-id (and (tfollower-key-block follower) (tfollower-key-id follower) (id-plist (tfollower-key-id follower)))
                         :shards (mapcar (lambda (e) (list :id (id-plist (getf e :id)) :state-hash (octets->hex (getf e :state-hash))))
                                         (tfollower-shards follower)))
                   f)))
        (uiop:rename-file-overwriting-target tmp path)
        (when (and (tfollower-key-block follower) (tfollower-key-id follower))
          (let ((boc-tmp (format nil "~A.key.boc.tmp" path)) (octets (serialize-boc (tfollower-key-block follower))))
            (with-open-file (f boc-tmp :direction :output :if-exists :supersede :element-type '(unsigned-byte 8))
              (write-sequence octets f))
            (uiop:rename-file-overwriting-target boc-tmp (format nil "~A.key.boc" path))))))
    path))

(defun tonnode-follower-restore (follower &optional (path (tfollower-state-file follower)))
  "Load what TONNODE-FOLLOWER-SAVE wrote into FOLLOWER; true when PATH was read.  A missing or damaged file leaves FOLLOWER alone."
  (let ((data (and path (probe-file path) (ignore-errors (with-open-file (f path :external-format :utf-8) (let ((*read-eval* nil)) (read f)))))))
    (when (and (consp data) (eql 1 (getf data :follower)))
      (flet ((plist-id (p) (tl-make "tonNode.blockIdExt" :workchain (getf p :workchain) :shard (getf p :shard) :seqno (getf p :seqno)
                                                         :root-hash (hex->octets (getf p :root-hash)) :file-hash (hex->octets (getf p :file-hash)))))
        (let ((shards (ignore-errors (mapcar (lambda (e) (list :id (plist-id (getf e :id)) :state-hash (hex->octets (getf e :state-hash))))
                                             (getf data :shards)))))
          (when (or shards (null (getf data :shards)))
            (setf (tfollower-shards follower) shards
                  (tfollower-mc-id follower) (and (getf data :mc-id) (plist-id (getf data :mc-id))))
            ;; the key block: its file must be there and its root cell must hash to the root hash saved with the id
            (let* ((key-plist (getf data :key-id))
                   (key-file (format nil "~A.key.boc" path))
                   (octets (and key-plist (probe-file key-file)
                                (ignore-errors (with-open-file (f key-file :element-type '(unsigned-byte 8))
                                                 (let ((v (make-array (file-length f) :element-type '(unsigned-byte 8)))) (read-sequence v f) v)))))
                   (root (and octets (ignore-errors (first (parse-boc octets))))))
              (when (and root (equalp (node-hash-at root 0) (hex->octets (getf key-plist :root-hash))))
                (setf (tfollower-key-block follower) root (tfollower-key-id follower) (plist-id key-plist))))
            t))))))

(defun tonnode-follower-step (follower mc-pool shard-pool mc-id &key (workchain 0) (max-blocks 32) (timeout 30) (prefetch t) (parallel 6))
  "Move FOLLOWER to the masterchain block MC-ID, whose id the caller got from anywhere (an untrusted supplier): the block is proven by
the validator set of the follower's key block (TONNODE-VERIFIED-MASTERCHAIN-BLOCK) and the basechain shards it commits to are taken in
(TONNODE-FOLLOWER-APPLY).  A key block becomes the new KEY-BLOCK (it was signed by the old set).  Nothing changes when something fails.
A step that has more than a few masterchain blocks to cover first reads the shard block ids from the masterchain blocks between and
fetches the blocks PARALLEL at a time (PREFETCH; %FOLLOWER-PREFETCH, *TONNODE-PREFETCH-STATS*): the walk then finds them in a cache; when
that fails the walk fetches them itself, as before.  The state file, when there is one, is written at the end.  (VALUES NEW-BLOCKS INFO
MC-STATE-HASH RESYNCED)."
  (multiple-value-bind (block info state-hash shards) (tonnode-verified-masterchain-block mc-pool mc-id (tfollower-key-block follower) :timeout timeout)
    (multiple-value-bind (new-blocks resynced)
        (tonnode-follower-apply follower shard-pool shards :workchain workchain :max-blocks max-blocks :timeout timeout
                                :cache (and prefetch (handler-case (%follower-prefetch follower mc-pool shard-pool mc-id shards workchain parallel timeout)
                                                       (error () nil))))
      (when (getf info :key-block) (setf (tfollower-key-block follower) block (tfollower-key-id follower) mc-id))
      (setf (tfollower-mc-id follower) mc-id)
      (tonnode-follower-save follower)
      (values new-blocks info state-hash resynced))))

(defun %mc-block-checked (b)
  "(VALUES INFO NEW-STATE-HASH) of the masterchain block plist B (:ID :BLOCK): the cell must be a Block whose header agrees with the id and
whose state_update is a Merkle update.  A PROOF-ERROR otherwise."
  (let ((root (getf b :block)) (id (getf b :id)))
    (unless (and (cell-p root) (not (cell-exotic-p root)) (= (load-uint (cell-slice root) 32) #x11ef55aa) (= 4 (length (cell-refs root))))
      (error 'proof-error :format-control "masterchain block ~D is not a Block" :format-arguments (list (tl-get id :seqno))))
    (let ((info (parse-block-info (svref (cell-refs root) 0))) (update (svref (cell-refs root) 2)))
      (unless (and (= (getf info :seqno) (tl-get id :seqno)) (= (getf info :workchain) (tl-get id :workchain))
                   (= (getf info :shard) (ldb (byte 64 0) (tl-get id :shard))))
        (error 'proof-error :format-control "masterchain block ~D: its header disagrees with its id" :format-arguments (list (tl-get id :seqno))))
      (unless (eql 4 (cell-special-type update))
        (error 'proof-error :format-control "masterchain block ~D: the state_update is not a Merkle update" :format-arguments (list (tl-get id :seqno))))
      (multiple-value-bind (old new) (merkle-update-hashes update)
        (declare (ignore old))
        (values info new)))))

(defun tonnode-follower-advance (follower mc-pool shard-pool &key (workchain 0) (max-blocks 300) (max-mc 300) (timeout 30) (parallel 6) (mc-deadline 45))
  "Move FOLLOWER on to the newest masterchain block the nodes have a proof for, with no supplier of ids: the masterchain blocks after
the follower's own one come from the nodes (downloadNextBlocksFull: block AND proof, batches of 10), they must hang together by their
predecessor references from the follower's block (a PROOF-ERROR otherwise), and the newest one is proven by the signatures of the
validator set of the follower's key block (a key block ends the range: it is the newest one taken, and the next call goes on from
it).  The blocks between are then trusted by the hash chain, their shard descriptions name the shard blocks to fetch side by side
(see %FOLLOWER-PREFETCH: the same cache), and the basechain shards of the newest are taken in as by TONNODE-FOLLOWER-APPLY.  Nothing
changes when something fails.  (VALUES NEW-BLOCKS INFO MC-STATE-HASH RESYNCED SIGNED-WEIGHT TOTAL-WEIGHT) as TONNODE-FOLLOWER-STEP; all NIL
when the nodes have no newer masterchain block with a proof yet.  The follower must have a masterchain block (a first step, see
TONNODE-FOLLOWER-STEP); further than about MAX-MC blocks behind, a step from a fresh id (a resync) is the better way.
The three kinds of work overlap: while the next masterchain blocks are fetched (one query each, about a fifth of a second) the shard
blocks they name are already downloaded and read by the PREFETCHER's threads, so that the walk at the end only checks the links.
*TONNODE-PREFETCH-STATS* tells what was read and fetched.  MC-DEADLINE is the number of seconds the masterchain read may take
(it ends then with the blocks read so far, the newest of them is proven): a follower that has caught up should use a small one (10-15),
else every step lasts the whole 45 s whatever is new (real run 2026-11-17: steps of 45-60 s, the proven block 8-16 s old)."
  (let ((old (tfollower-mc-id follower)))
    (unless old (error 'tonnode-error :format-control "the follower has no masterchain block to go on from: take a first step (TONNODE-FOLLOWER-STEP)" :format-arguments nil))
    (setf *tonnode-prefetch-stats* nil)
    (let* ((t0 (%tn-now))
           (held (mapcar (lambda (e) (getf e :id)) (tfollower-shards follower)))
           (pf (tonnode-start-prefetcher shard-pool :parallel parallel :timeout (min timeout 15) :deadline 150))
           (ok nil))
      (unwind-protect
           (let* ((batches nil)
                  (chain (multiple-value-bind (blocks b)
                             (tonnode-masterchain-range mc-pool old nil :max-blocks max-mc :timeout (min timeout 12) :deadline mc-deadline
                                                        :on-block (lambda (blk)
                                                                    (prefetcher-add pf (remove-if (lambda (i) (member i held :test #'%same-block-id-p))
                                                                                                  (%hint-shard-ids (list blk) workchain)))))
                           (setf batches b) blocks))
                  (t1 (%tn-now)))
             (setf *tonnode-prefetch-stats* (list :mc-blocks (length chain) :mc-seconds (- t1 t0) :batches batches :ids 0 :fetched 0 :failed 0 :bytes 0 :seconds 0))
             (when (null chain) (return-from tonnode-follower-advance (values nil nil nil nil nil nil)))
             (let ((key-pos (position-if (lambda (b) (getf (ignore-errors (parse-block-info (svref (cell-refs (getf b :block)) 0))) :key-block)) chain)))
               (when key-pos (setf chain (subseq chain 0 (1+ key-pos)))))
             (let ((prev-id old))
               (dolist (b chain)
                 (let ((links (parse-block-links (getf b :block) (getf b :id))))
                   (unless (and (= 1 (length links)) (%same-block-id-p (shard-descr-block-id (first links)) prev-id))
                     (error 'proof-error :format-control "masterchain block ~D does not follow the block ~D before it" :format-arguments (list (tl-get (getf b :id) :seqno) (tl-get prev-id :seqno)))))
                 (setf prev-id (getf b :id))))
             (let* ((newest (car (last chain))) (id (getf newest :id)) (block (getf newest :block)))
               (unless (getf newest :proof) (error 'tonnode-error :format-control "the nodes sent no proof of masterchain block ~D" :format-arguments (list (tl-get id :seqno))))
               (multiple-value-bind (info state-hash) (%mc-block-checked newest)
                 (multiple-value-bind (proof-info weight total)
                     (verify-node-block-proof-by-key-block (serialize-boc (getf newest :proof)) id (tfollower-key-block follower))
                   (declare (ignore proof-info))
                   (let ((shards (block-shard-descriptions block)))
                     (prefetcher-add pf (loop for d in shards when (= workchain (getf d :workchain)) collect (shard-descr-block-id d)))
                     (multiple-value-bind (cache stats) (prefetcher-finish pf)
                       (setf ok t)
                       (setf *tonnode-prefetch-stats* (list* :mc-blocks (length chain) :mc-seconds (- t1 t0) :batches batches stats))
                       (multiple-value-bind (new-blocks resynced)
                           (tonnode-follower-apply follower shard-pool shards :workchain workchain :max-blocks max-blocks :timeout timeout :cache cache)
                         (when (getf info :key-block) (setf (tfollower-key-block follower) block (tfollower-key-id follower) id))
                         (setf (tfollower-mc-id follower) id)
                         (tonnode-follower-save follower)
                         (values new-blocks info state-hash resynced weight total))))))))
        (unless ok (prefetcher-finish pf :abort t))))))

(defun tonnode-follower-run (follower mc-pool shard-pool
                             &key head-fn watchlist read-fn on-step on-error stop steps (pause 1) (max-failures 5) (resync-after 2)
                                  (max-lag 380) (resync-age 120)
                                  (workchain 0) (max-blocks 300) (max-mc 300) (timeout 20) (parallel 6) (mc-deadline 12))
  "Keep FOLLOWER on the newest masterchain block the nodes have a proof for, step after step (TONNODE-FOLLOWER-ADVANCE), until STEPS
steps were made (NIL: for ever) or the function STOP returns true; the number of steps is returned.
HEAD-FN (optional) returns a masterchain blockIdExt from anyone (a liteserver will do: the block is proven by the validators' signatures
before anything is believed of it).  It is asked for a first step when the follower has no masterchain block, and BEFORE A STEP when the
follower may be behind: on the first step of the run, after a step whose proven block was more than RESYNC-AGE seconds old, and after
RESYNC-AFTER failures in a row.  When that head is MAX-LAG or more masterchain blocks ahead of the follower, the step is a fresh one from
the head id (TONNODE-FOLLOWER-STEP: what the skipped blocks changed is not seen, see RESYNCED), as walking a long way block by block
cannot catch up (real run 2026-11-17: a follower 8 hours behind gained 13 s of chain per 15 s step and never arrived); otherwise it goes
on by advance.  Without HEAD-FN there is no such check.
A TONNODE-ERROR or PROOF-ERROR of a step (or an error of HEAD-FN, taken for a TONNODE-ERROR) changes nothing in the follower (see the step functions): ON-ERROR is called with the condition
and the number of failures in a row, the loop sleeps PAUSE seconds and tries again, and the error is signalled after MAX-FAILURES in a
row.  A step the nodes have nothing new for just waits PAUSE seconds.  After every step that moved the follower, WATCHLIST (a
TONNODE-WATCHLIST, optional) takes in its blocks (TONNODE-WATCH-BLOCKS) and ON-STEP is called with a plist (:NEW-BLOCKS :INFO :STATE-HASH
:RESYNCED :WEIGHT :TOTAL :FRESH true when the step was a fresh one :EVENTS the watchlist's events :SECONDS what the step took).  A
PROOF-ERROR of the watchlist is not swallowed: a block that disagrees with itself is not a thing to retry.  With READ-FN (see
TONNODE-WATCH-REFRESH) the accounts of the watchlist that are stale (not seen yet, or skipped by a resync) are read again after every step."
  (let ((done 0) (failures 0) (maybe-behind t))
    (loop
      (when (or (and steps (>= done steps)) (and stop (funcall stop))) (return done))
      (let* ((start (%tn-now))
             (result
               (handler-case
                   (let* ((mc (tfollower-mc-id follower))
                          (head (and head-fn (or (null mc) maybe-behind (>= failures resync-after))
                                     ;; whoever supplies the head (a liteserver) may be down or silent: that is a failed step like the others
                                     (handler-case (funcall head-fn)
                                       (error (e) (error 'tonnode-error :format-control "the head id could not be had: ~A: ~A"
                                                                        :format-arguments (list (type-of e) e))))))
                          (fresh (and head (or (null mc) (>= failures resync-after)
                                               (>= (- (tl-get head :seqno) (tl-get mc :seqno)) max-lag)))))
                     (when (and (null mc) (null head))
                       (error 'tonnode-error :format-control "the follower has no masterchain block and there is no HEAD-FN to take a first step from"
                                             :format-arguments nil))
                     (multiple-value-bind (blocks info mc-hash resynced weight total)
                         (if fresh
                             (tonnode-follower-step follower mc-pool shard-pool head :workchain workchain :max-blocks max-blocks
                                                                                      :timeout timeout :parallel parallel)
                             (tonnode-follower-advance follower mc-pool shard-pool :workchain workchain :max-blocks max-blocks :max-mc max-mc
                                                                                   :timeout timeout :parallel parallel :mc-deadline mc-deadline))
                       (setf failures 0)
                       (if info
                           (progn (setf maybe-behind (> (- (unix-now) (getf info :gen-utime)) resync-age))
                                  (list :new-blocks blocks :info info :state-hash mc-hash :resynced resynced :weight weight :total total :fresh (and fresh t)))
                           :nothing)))
                 ((or tonnode-error proof-error) (e)
                   (incf failures)
                   (when on-error (funcall on-error e failures))
                   (when (>= failures max-failures) (error e))
                   :failed))))
        (cond ((eq result :nothing) (sleep pause))
              ((eq result :failed) (sleep pause))
              (t (incf done)
                 (let ((events (and watchlist (tonnode-watch-blocks watchlist (getf result :new-blocks) (getf result :resynced)))))
                   (when (and watchlist read-fn)
                     (tonnode-watch-refresh watchlist follower read-fn))
                   (when on-step
                     (funcall on-step (list* :events events :seconds (- (%tn-now) start) result))))))))))

;;; ---------------------------------------------------------------------------------------------------------------------------------
;;; The watchlist (Phase 5, hot path): accounts followed block by block, with no download beyond the blocks the follower reads anyway
;;; ---------------------------------------------------------------------------------------------------------------------------------

(defstruct (tonnode-watchlist (:copier nil))
  "Accounts of one workchain whose newest state is kept from the blocks of a tonNode follower.  TABLE maps the lower-case hex of the
32 account octets to a plist (:EXISTS :BALANCE :ACCOUNT-CELL :LAST-TRANS-LT :LAST-TRANS-HASH :BLOCK-ID the shard block it came from
:STATE-HASH that block's new state hash :STALE).  An entry is STALE when the follower skipped blocks that may have changed the account
(RESYNC) or when it was never seen: it has to be read again (LITE-ACCOUNT-STATE-AT, then TONNODE-WATCH-SET) before it is believed."
  (table (make-hash-table :test 'equal)))

(defun %watch-key (account)
  (if (stringp account) (string-downcase account) (octets->hex account)))

(defun tonnode-watch-add (watchlist account)
  "Put ACCOUNT (32 octets or their hex) on WATCHLIST, stale until a state is set.  Returns the hex key."
  (let ((key (%watch-key account)))
    (unless (gethash key (tonnode-watchlist-table watchlist))
      (setf (gethash key (tonnode-watchlist-table watchlist)) (list :stale t)))
    key))

(defun tonnode-watch-remove (watchlist account)
  (remhash (%watch-key account) (tonnode-watchlist-table watchlist)) nil)

(defun tonnode-watch-get (watchlist account)
  "The entry of ACCOUNT (plist, see TONNODE-WATCHLIST) or NIL when it is not watched."
  (values (gethash (%watch-key account) (tonnode-watchlist-table watchlist))))

(defun tonnode-watch-stale (watchlist)
  "The hex keys of the watched accounts that have to be read again."
  (loop for key being the hash-keys of (tonnode-watchlist-table watchlist) using (hash-value entry)
        when (getf entry :stale) collect key))

;; the balance of an Account cell (a cold read gives the cell, not the DepthBalanceInfo that a block's state update reveals)
(defun account-cell-balance (account-cell)
  "The balance in nanotons of ACCOUNT-CELL, an Account (account$1 addr storage_stat storage: StorageInfo = used (cells, bits), storage_extra, last_paid,
due_payment; then last_trans_lt, balance); real mainnet block 108759255 has accounts of both kinds of storage_extra; 0 for
account_none$0.  Code and data may be pruned: only the header is read.  Anycast addresses are not read (error)."
  (let ((s (cell-slice account-cell)))
    (multiple-value-bind (tag s) (load-uint s 1)
      (if (zerop tag)
          0
          (multiple-value-bind (atag s) (load-uint s 2)
            (unless (= atag 2) (error "an Account with an address that is not addr_std"))
            (multiple-value-bind (anycast s) (load-uint s 1)
              (unless (zerop anycast) (error "an Account with an anycast address"))
              (let ((s (skip-bits s (+ 8 256))))
                (dotimes (i 2)             ; StorageUsed: cells, bits: VarUInteger 7 each
                  (multiple-value-bind (len s2) (load-uint s 3) (setf s (skip-bits s2 (* 8 len)))))
                ;; then StorageExtraInfo (storage_extra_none$000, storage_extra_info$001 dict_hash:uint256); in the older layout the third
                ;; VarUInteger 7 of StorageUsed (public_cells, always 0: the same three zero bits) stood here
                (multiple-value-bind (extra s2) (load-uint s 3)
                  (setf s (cond ((= extra 0) s2) ((= extra 1) (skip-bits s2 256)) (t (skip-bits s2 (* 8 extra))))))
                (setf s (skip-bits s 32))  ; last_paid
                (multiple-value-bind (due s2) (load-uint s 1)
                  (setf s (if (= due 1) (nth-value 1 (load-coins s2)) s2)))
                (setf s (skip-bits s 64))  ; last_trans_lt
                (values (load-coins s)))))))))

(defun tonnode-watch-set (watchlist account state shard-block-id state-hash)
  "Record STATE, the plist of LITE-ACCOUNT-STATE-AT (or of BLOCK-NEW-SHARD-ACCOUNT), for a watched ACCOUNT, as proved against the shard
state STATE-HASH of the shard block SHARD-BLOCK-ID.  A state read from a block OLDER than the one the entry came from is not taken
(NIL returned): a late cold read never moves an account back."
  (let* ((key (%watch-key account)) (old (gethash key (tonnode-watchlist-table watchlist))))
    (when (and old (not (getf old :stale)) (getf old :block-id) shard-block-id
               (= (tl-get (getf old :block-id) :shard) (tl-get shard-block-id :shard))
               (> (tl-get (getf old :block-id) :seqno) (tl-get shard-block-id :seqno)))
      (return-from tonnode-watch-set nil))
    (setf (gethash key (tonnode-watchlist-table watchlist))
          (list :exists (getf state :exists)
                :balance (or (getf state :balance) (and (getf state :exists) (getf state :account-cell) (account-cell-balance (getf state :account-cell))))
                :account-cell (getf state :account-cell)
                :last-trans-lt (getf state :last-trans-lt) :last-trans-hash (getf state :last-trans-hash)
                :block-id shard-block-id :state-hash state-hash :stale nil))
    t))

(defun tonnode-watch-refresh (watchlist follower read-fn)
  "Read every STALE account of WATCHLIST again.  READ-FN gets the 32 octets of the account and the follower's masterchain block id and returns
the plist of LITE-ACCOUNT-STATE-AT (a proof against the state of that block, the liteserver is not believed).  A state is taken only when
the shard block its proof names is a tip of FOLLOWER and the proved state hash is the one the follower holds for that tip (so it is the
state the blocks that follow are applied to).  An error of READ-FN leaves the account stale.  Returns the hex keys refreshed."
  (let ((mc (tfollower-mc-id follower)) (done '()))
    (when mc
      (dolist (key (tonnode-watch-stale watchlist))
        (handler-case
            (let* ((r (funcall read-fn (hex->octets key) mc)) (shard (getf r :shard-block))
                   (tip (and shard (find-if (lambda (e) (%same-block-id-p (getf e :id) shard)) (tfollower-shards follower)))))
              (when (and tip (equalp (getf r :state-hash) (getf tip :state-hash)))
                (tonnode-watch-set watchlist key r shard (getf r :state-hash))
                (push key done)))
          (error () nil))))
    (nreverse done)))

(defun %watch-in-shard-p (shard account)
  "SHARD the signed 64-bit shard id, ACCOUNT its 32 octets: does the shard hold the account?"
  (let* ((s (ldb (byte 64 0) shard)) (low (logand s (- s)))
         (mask (logand (lognot (1- (* 2 low))) #xFFFFFFFFFFFFFFFF)))
    (= (logand (octets->uint account :end 8) mask) (logand (- s low) mask))))

(defun tonnode-watch-blocks (watchlist new-blocks &optional resynced)
  "Take in NEW-BLOCKS (the first value of TONNODE-FOLLOWER-APPLY/-ADVANCE: oldest first within a shard) and RESYNCED (its second): for
every watched account a block changed, the new ShardAccount is read from the block's state update (BLOCK-NEW-SHARD-ACCOUNT) and
cross-checked against the block's AccountBlock (last transaction lt and hash, hash of the Account cell): a disagreement is a
PROOF-ERROR and changes nothing of that block.  Accounts in a resynced shard become STALE (blocks were skipped: what they changed was
not seen).  Returns the events, oldest first, plists (:ACCOUNT hex :BLOCK-ID :TRANSACTIONS how many in that block :EXISTS :BALANCE
:LAST-TRANS-LT :LAST-TRANS-HASH :ACCOUNT-CELL).  Only blocks that name a watched account are read beyond their account list."
  (let ((events '()) (table (tonnode-watchlist-table watchlist)))
    (dolist (r resynced)
      (let ((shard (tl-get (getf r :id) :shard)))
        (loop for key being the hash-keys of table using (hash-value entry)
              when (%watch-in-shard-p shard (hex->octets key))
                do (setf (gethash key table) (list* :stale t (loop for (k v) on entry by #'cddr unless (eq k :stale) append (list k v)))))))
    (when (plusp (hash-table-count table))
      (dolist (b new-blocks)
        (let ((block (getf b :block)) (id (getf b :id)))
          (when block
            (dolist (change (block-account-changes block))
              (let* ((hex (octets->hex (getf change :account))) (entry (gethash hex table)))
                (when entry
                  (let ((account (block-new-shard-account block (getf change :account))))
                    (unless (or (not (getf account :exists))
                                (and (getf account :exists)
                                 (= (getf account :last-trans-lt) (getf change :last-lt))
                                 (equalp (getf account :last-trans-hash) (getf change :last-trans-hash))
                                 (equalp (node-hash-at (getf account :account-cell) 0) (getf change :new-account-hash))))
                      (error 'proof-error :format-control "block ~D: the new state of account ~A does not agree with its AccountBlock"
                                          :format-arguments (list (tl-get id :seqno) hex)))
                    (setf (gethash hex table)
                          (list :exists (getf account :exists) :balance (getf account :balance) :account-cell (getf account :account-cell)
                                :last-trans-lt (getf account :last-trans-lt) :last-trans-hash (getf account :last-trans-hash)
                                :block-id id :state-hash (getf b :state-hash) :stale nil))
                    (push (list :account hex :block-id id :transactions (getf change :transactions) :exists (getf account :exists)
                                :balance (getf account :balance) :last-trans-lt (getf account :last-trans-lt)
                                :last-trans-hash (getf account :last-trans-hash) :account-cell (getf account :account-cell))
                          events)))))))))
    (nreverse events)))
