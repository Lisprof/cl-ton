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

;;;; rldp.lisp -- RLDP2, the reliable large datagram protocol of the TON node (rldp2/), a query/answer layer for data of any
;;;; size over lossy datagrams.
;;;;
;;;; From the node's sources (rldp2/RldpConnection.cpp, InboundTransfer.cpp, RldpReceiver.cpp, Ack.cpp, OutboundTransfer.h):
;;;;  * a QUERY is a boxed rldp.query {query_id, max_answer_size, timeout, data} sent as a TRANSFER; the ANSWER is a boxed
;;;;    rldp.answer {query_id, data} sent as a transfer whose id is the query transfer's id with every octet XORed with #xFF;
;;;;  * a transfer of TOTAL-SIZE octets is cut into parts of 2,000,000 octets (the last one shorter); every part is coded with
;;;;    RaptorQ (src/raptorq.lisp) in symbols of 768 octets; the sender sends rldp2.messagePart {transfer_id, fec.raptorQ
;;;;    {data_size = the part's size, symbol_size = 768, symbols_count = K}, part, total_size, seqno = the symbol id, data}
;;;;    and keeps sending new symbols until it is told the part is complete;
;;;;  * the receiver numbers packets from seqno+1 in an Ack {max_seqno, a 32-bit mask of the last 32 packets, received_count},
;;;;    answers new packets with rldp2.confirm after 1 ms (then again after 2, 4 ... 128 ms while nothing new comes), and a
;;;;    finished part with rldp2.complete {transfer_id, part}; a part of a finished transfer is answered with complete again;
;;;;  * a duplicate packet is not fed to the decoder; wrong symbol sizes, part sizes or part numbers are dropped.
;;;; The messages travel as custom ADNL messages; this file does not know the transport: it is given a SEND function (octets of
;;;; one boxed rldp2 message), is fed incoming messages with RLDP-RECEIVE and is driven by RLDP-TICK with an explicit clock, so
;;;; loss and reordering can be simulated exactly.  This sender is the minimal one (bursts of fresh symbols until a complete
;;;; arrives, no congestion control): meant for queries, which are small; the answers the node sends use its own pacing.
;;;; A connection is a client unless it is given an ON-QUERY function, which makes it answer queries (used to test against a
;;;; node-like peer).

(in-package :cl-ton)

(defconstant +rldp-symbol-size+ 768 "The only symbol size RLDP2 accepts (OutboundTransfer::symbol_size).")
(defconstant +rldp-part-size+ 2000000 "OutboundTransfer::part_size: the size of a part of a transfer.")

(define-condition rldp-timeout (ton-error) ())

(defparameter *rldp-ack-delay* 0.001d0 "Seconds from a new packet to the confirm, and the base of the doubling resends.")
(defparameter *rldp-resend-interval* 0.25d0 "Seconds between bursts of fresh symbols of a small part (no complete yet).")
(defparameter *rldp-burst* 32 "At most this many symbols per burst.")
(defparameter *rldp-max-parts-in-progress* 20 "InboundTransfer: at most this many parts of a transfer are buffered.")
(defparameter *rldp-completed-memory* 20d0 "Seconds a finished transfer is remembered to answer stray packets with complete.")

(defun rldp-clock ()
  "The wall clock in seconds (a double) for RLDP-TICK and friends."
  (/ (get-internal-real-time) (float internal-time-units-per-second 1d0)))

;;; --- Ack (rldp2/Ack.cpp)

(defstruct (rldp-ack (:conc-name rack-) (:copier nil))
  (max-seqno 0 :type (unsigned-byte 32)) (mask 0 :type (unsigned-byte 32)) (count 0 :type (unsigned-byte 32)))

(defun %rldp-ack-got (ack seqno)
  "Record the packet SEQNO (numbered from 1); true when it is new."
  (when (> seqno (rack-max-seqno ack))
    (let ((diff (- seqno (rack-max-seqno ack))))
      (setf (rack-mask ack) (if (>= diff 32) 0 (ldb (byte 32 0) (ash (rack-mask ack) diff))))
      (setf (rack-max-seqno ack) seqno)))
  (let ((offset (- (rack-max-seqno ack) seqno)))
    (when (< offset 32)
      (let ((bit (ash 1 offset)))
        (when (zerop (logand (rack-mask ack) bit))
          (incf (rack-count ack))
          (setf (rack-mask ack) (logior (rack-mask ack) bit))
          t)))))

(defun %rldp-s32 (unsigned) (if (>= unsigned (ash 1 31)) (- unsigned (ash 1 32)) unsigned))

;;; --- state

(defstruct (rldp-in-part (:conc-name rip-) (:copier nil))
  decoder (ack (make-rldp-ack)) (ack-at nil) (ack-count 0 :type fixnum))

(defstruct (rldp-in (:conc-name rin-) (:copier nil))
  id (total-size 0 :type fixnum) (n-parts 1 :type fixnum) (parts (make-hash-table)) (pieces nil) (done 0 :type fixnum)
  (max-size 0 :type fixnum) (deadline 0d0 :type double-float) kind query-id)

(defstruct (rldp-out-part (:conc-name rop-) (:copier nil))
  encoder (symbols-count 1 :type fixnum) (data-size 0 :type fixnum) (next-id 0 :type fixnum) (next-at 0d0 :type double-float)
  (done nil) (received-count 0 :type fixnum))

(defstruct (rldp-out (:conc-name rout-) (:copier nil))
  id (total-size 0 :type fixnum) parts (deadline 0d0 :type double-float))

(defstruct (rldp-pending (:conc-name rpend-) (:copier nil))
  query-id answer-id transfer-id max-size (deadline 0d0 :type double-float)
  (semaphore (sb-thread:make-semaphore)) (answer nil))

(defstruct (rldp-connection (:conc-name rldpc-) (:constructor %make-rldp-connection) (:copier nil))
  (send nil :type function) (on-query nil)
  (lock (sb-thread:make-mutex :name "rldp"))
  (inbound (make-hash-table :test 'equalp)) (outbound (make-hash-table :test 'equalp))
  (completed (make-hash-table :test 'equalp))      ; transfer id -> time until which it is remembered
  (pending (make-hash-table :test 'equalp))        ; query id -> rldp-pending
  (outbox '())
  (packets 0 :type fixnum) (duplicates 0 :type fixnum) (parts 0 :type fixnum) (repaired 0 :type fixnum))

(defun make-rldp-connection (send &key on-query)
  "A connection to one peer.  SEND is called with the octets of every boxed rldp2 message to transmit (as one custom ADNL
message).  ON-QUERY, when given, makes the connection answer queries: (funcall ON-QUERY data) returns the answer octets or NIL."
  (%make-rldp-connection :send send :on-query on-query))

(defun %rldp-emit (conn object)
  (push (tl-encode object) (rldpc-outbox conn)))

(defun %rldp-flush (conn)
  "Send what the locked section queued; never called with the lock held (SEND may take other locks)."
  (let ((messages (sb-thread:with-mutex ((rldpc-lock conn))
                    (prog1 (nreverse (rldpc-outbox conn)) (setf (rldpc-outbox conn) '())))))
    (dolist (m messages) (funcall (rldpc-send conn) m))))

(defmacro %with-rldp ((conn) &body body)
  "Run BODY under the connection's lock, then send what it queued."
  (let ((c (gensym "CONN")))
    `(let ((,c ,conn))
       (multiple-value-prog1 (sb-thread:with-mutex ((rldpc-lock ,c)) ,@body)
         (%rldp-flush ,c)))))

(defun %rldp-complement (id)
  (let ((out (make-array (length id) :element-type '(unsigned-byte 8))))
    (dotimes (i (length id) out) (setf (aref out i) (logxor #xFF (aref id i))))))

;;; --- sending a transfer

(defun %rldp-part-count (size) (max 1 (ceiling size +rldp-part-size+)))

(defun %rldp-start-transfer (conn id data now deadline)
  (let* ((data (coerce data 'tl-octets)) (n (%rldp-part-count (length data))) (parts (make-array n)))
    (dotimes (i n)
      (let* ((start (* i +rldp-part-size+)) (chunk (subseq data start (min (length data) (+ start +rldp-part-size+))))
             (encoder (make-rq-encoder chunk +rldp-symbol-size+)))
        (unless encoder (error 'ton-error :format-control "RLDP: ~D octets are too big for one part" :format-arguments (list (length chunk))))
        (setf (aref parts i) (make-rldp-out-part :encoder encoder :symbols-count (rq-encoder-symbols-count encoder)
                                                 :data-size (length chunk) :next-at now))))
    (let ((out (make-rldp-out :id id :total-size (length data) :parts parts :deadline deadline)))
      (setf (gethash id (rldpc-outbound conn)) out)
      (%rldp-pump-out conn out now)
      out)))

(defun %rldp-pump-out (conn out now)
  "Send a burst of fresh symbols of every unfinished part that is due."
  (loop for part across (rout-parts out) for index from 0
        when (and (not (rop-done part)) (>= now (rop-next-at part)))
          do (let ((k (rop-symbols-count part)))
               (dotimes (j (min *rldp-burst* (1+ k)))
                 (let ((id (rop-next-id part)))
                   (incf (rop-next-id part))
                   (%rldp-emit conn (tl-make "rldp2.messagePart"
                                             :transfer-id (coerce (rout-id out) 'tl-octets)
                                             :fec-type (tl-make "fec.raptorQ" :data-size (rop-data-size part)
                                                                              :symbol-size +rldp-symbol-size+ :symbols-count k)
                                             :part index :total-size (rout-total-size out) :seqno id
                                             :data (coerce (rq-encoder-symbol (rop-encoder part) id) 'tl-octets)))))
               (setf (rop-next-at part) (+ now (if (<= k *rldp-burst*) *rldp-resend-interval* (/ *rldp-resend-interval* 8)))))))

;;; --- receiving

(defun %rldp-on-complete (conn msg)
  (let* ((id (as-octets (tl-get msg :transfer-id))) (out (gethash id (rldpc-outbound conn))) (index (tl-get msg :part)))
    (when (and out (< -1 index (length (rout-parts out))))
      (setf (rop-done (aref (rout-parts out) index)) t)
      (when (every #'rop-done (rout-parts out))
        (remhash id (rldpc-outbound conn))))))

(defun %rldp-on-confirm (conn msg)
  (let* ((id (as-octets (tl-get msg :transfer-id))) (out (gethash id (rldpc-outbound conn))) (index (tl-get msg :part)))
    (when (and out (< -1 index (length (rout-parts out))))
      (let ((part (aref (rout-parts out) index)))
        (setf (rop-received-count part) (max (rop-received-count part) (ldb (byte 32 0) (tl-get msg :received-count))))))))

(defun %rldp-new-inbound (conn id total-size now)
  "The inbound record for the unknown transfer ID, or NIL when we expect no such transfer."
  (let ((pending (loop for p being the hash-values of (rldpc-pending conn) when (equalp (rpend-answer-id p) id) return p)))
    (cond (pending
           (when (<= total-size (+ (rpend-max-size pending) 4096))
             (make-rldp-in :id id :total-size total-size :n-parts (%rldp-part-count total-size) :kind :answer
                           :query-id (rpend-query-id pending) :max-size (+ (rpend-max-size pending) 4096)
                           :deadline (+ now 10d0))))
          ((rldpc-on-query conn)
           (when (<= total-size (* 4 +rldp-part-size+))
             (make-rldp-in :id id :total-size total-size :n-parts (%rldp-part-count total-size) :kind :query
                           :max-size (* 4 +rldp-part-size+) :deadline (+ now 10d0)))))))

(defun %rldp-on-part (conn msg now)
  (let* ((id (as-octets (tl-get msg :transfer-id))) (index (tl-get msg :part)) (total (tl-get msg :total-size))
         (fec (tl-get msg :fec-type)) (seqno (tl-get msg :seqno)) (data (as-octets (tl-get msg :data))))
    (when (gethash id (rldpc-completed conn))
      (%rldp-emit conn (tl-make "rldp2.complete" :transfer-id (coerce id 'tl-octets) :part index))
      (return-from %rldp-on-part))
    ;; what the node drops: a wrong fec type or symbol size, a part number or size that does not fit the total
    (unless (and (tl-is fec "fec.raptorQ") (= (tl-get fec :symbol-size) +rldp-symbol-size+)
                 (typep total 'fixnum) (plusp total) (typep index 'fixnum) (<= 0 seqno (1- (ash 1 24)))
                 (= (length data) +rldp-symbol-size+))
      (return-from %rldp-on-part))
    (let* ((n-parts (%rldp-part-count total))
           (expected (if (and (= (1+ index) n-parts) (plusp (mod total +rldp-part-size+))) (mod total +rldp-part-size+) +rldp-part-size+))
           (data-size (tl-get fec :data-size)))
      (unless (and (< -1 index n-parts) (= data-size expected) (= (tl-get fec :symbols-count) (ceiling data-size +rldp-symbol-size+)))
        (return-from %rldp-on-part))
      (let ((in (or (gethash id (rldpc-inbound conn))
                    (let ((new (%rldp-new-inbound conn id total now)))
                      (when new
                        (setf (rin-pieces new) (make-array n-parts :initial-element nil))
                        (setf (gethash id (rldpc-inbound conn)) new)))))
            (part nil))
        (unless (and in (= (rin-total-size in) total)) (return-from %rldp-on-part))
        (when (aref (rin-pieces in) index)       ; a part we already have: tell the sender it is complete
          (%rldp-emit conn (tl-make "rldp2.complete" :transfer-id (coerce id 'tl-octets) :part index))
          (return-from %rldp-on-part))
        (setf part (or (gethash index (rin-parts in))
                       (when (< (hash-table-count (rin-parts in)) *rldp-max-parts-in-progress*)
                         (let ((decoder (make-rq-decoder data-size +rldp-symbol-size+)))
                           (when decoder (setf (gethash index (rin-parts in)) (make-rldp-in-part :decoder decoder)))))))
        (unless part (return-from %rldp-on-part))
        (if (not (%rldp-ack-got (rip-ack part) (1+ seqno)))
            (incf (rldpc-duplicates conn))
        (progn                                            ; a new packet
          (incf (rldpc-packets conn))
          (setf (rip-ack-count part) 0)
          (setf (rip-ack-at part) (min (or (rip-ack-at part) most-positive-double-float) (+ now *rldp-ack-delay*)))
          (when (rq-decoder-add (rip-decoder part) seqno data)
            (let ((decoded (rq-decoder-decode (rip-decoder part))))
              (when decoded
                (incf (rldpc-parts conn))
                (when (< (rq-decoder-source-count (rip-decoder part)) (rqp-k (rq-decoder-params (rip-decoder part))))
                  (incf (rldpc-repaired conn)))      ; some source symbol was missing: RaptorQ repair was needed
                (setf (aref (rin-pieces in) index) decoded)
                (remhash index (rin-parts in))
                (incf (rin-done in))
                (%rldp-emit conn (tl-make "rldp2.complete" :transfer-id (coerce id 'tl-octets) :part index)))))))
        (when (= (rin-done in) (rin-n-parts in))
          (remhash id (rldpc-inbound conn))
          (setf (gethash id (rldpc-completed conn)) (+ now *rldp-completed-memory*))
          (%rldp-deliver conn in (apply #'concatenate 'tl-octets (coerce (rin-pieces in) 'list)) now))))))

(defun %rldp-deliver (conn in data now)
  (let ((obj (ignore-errors (tl-decode data))))
    (case (rin-kind in)
      (:answer
       (when (and obj (tl-is obj "rldp.answer") (equalp (as-octets (tl-get obj :query-id)) (rin-query-id in)))
         (let ((pending (gethash (rin-query-id in) (rldpc-pending conn))))
           (when pending
             (setf (rpend-answer pending) (as-octets (tl-get obj :data)))
             (sb-thread:signal-semaphore (rpend-semaphore pending))))))
      (:query
       (when (and obj (tl-is obj "rldp.query"))
         (let ((answer (funcall (rldpc-on-query conn) (as-octets (tl-get obj :data)))))
           (when (and answer (<= (length answer) (tl-get obj :max-answer-size)))
             (%rldp-start-transfer conn (%rldp-complement (rin-id in))
                                   (tl-encode (tl-make "rldp.answer" :query-id (coerce (as-octets (tl-get obj :query-id)) 'tl-octets)
                                                                    :data (coerce answer 'tl-octets)))
                                   now (+ now 10d0)))))))))

(defun rldp-receive (conn octets &key (now (rldp-clock)))
  "Feed one incoming custom message (octets of a boxed rldp2 message) to CONN.  Anything malformed or unexpected is ignored."
  (let ((msg (ignore-errors (tl-decode octets))))
    (when msg
      (%with-rldp (conn)
        (cond ((tl-is msg "rldp2.messagePart") (%rldp-on-part conn msg now))
              ((tl-is msg "rldp2.confirm") (%rldp-on-confirm conn msg))
              ((tl-is msg "rldp2.complete") (%rldp-on-complete conn msg)))))
    nil))

;;; --- the clock: confirms, bursts, expiry

(defun rldp-tick (conn &optional (now (rldp-clock)))
  "Send the confirms and the symbol bursts that are due at NOW, drop what has expired; returns the time (same clock) at which
something is next due, or NIL."
  (%with-rldp (conn)
    (let ((wake nil))
      (flet ((note (time) (when time (setf wake (if wake (min wake time) time)))))
        (let ((dead '()))
          (maphash (lambda (id in)
                     (if (> now (rin-deadline in))
                         (push id dead)
                         (maphash (lambda (index part)
                                    (when (and (rip-ack-at part) (>= now (rip-ack-at part)))
                                      (let ((ack (rip-ack part)))
                                        (%rldp-emit conn (tl-make "rldp2.confirm" :transfer-id (coerce id 'tl-octets) :part index
                                                                                  :max-seqno (%rldp-s32 (rack-max-seqno ack))
                                                                                  :received-mask (%rldp-s32 (rack-mask ack))
                                                                                  :received-count (%rldp-s32 (rack-count ack))))
                                        (incf (rip-ack-count part))
                                        (setf (rip-ack-at part) (and (<= (rip-ack-count part) 7)
                                                                     (+ now (* *rldp-ack-delay* (ash 1 (rip-ack-count part))))))))
                                    (note (rip-ack-at part)))
                                  (rin-parts in))))
                   (rldpc-inbound conn))
          (dolist (id dead) (remhash id (rldpc-inbound conn))))
        (let ((dead '()))
          (maphash (lambda (id out)
                     (if (> now (rout-deadline out))
                         (push id dead)
                         (progn (%rldp-pump-out conn out now)
                                (loop for part across (rout-parts out) unless (rop-done part) do (note (rop-next-at part))))))
                   (rldpc-outbound conn))
          (dolist (id dead) (remhash id (rldpc-outbound conn))))
        (maphash (lambda (id until) (when (> now until) (remhash id (rldpc-completed conn)))) (rldpc-completed conn)))
      wake)))

(defun rldp-stats (conn)
  "A plist of what CONN has received so far: :PACKETS new symbols accepted, :DUPLICATES symbols dropped as already seen, :PARTS
parts decoded, :REPAIRED how many of those parts were missing source symbols and so needed RaptorQ repair."
  (list :packets (rldpc-packets conn) :duplicates (rldpc-duplicates conn) :parts (rldpc-parts conn) :repaired (rldpc-repaired conn)))

;;; --- queries

(defun rldp-query-start (conn data &key (timeout 5) (max-answer-size 1048576) (now (rldp-clock)))
  "Start the query DATA (the octets of the function to run, for example overlay.query + tonNode.getCapabilities): send the
rldp.query transfer and expect the answer; returns the pending record (see RLDP-PENDING-ANSWER)."
  (%with-rldp (conn)
    (let* ((query-id (ironclad:random-data 32)) (transfer-id (ironclad:random-data 32))
           (deadline (+ now timeout))
           (pending (make-rldp-pending :query-id query-id :transfer-id transfer-id :answer-id (%rldp-complement transfer-id)
                                       :max-size max-answer-size :deadline deadline))
           (query (tl-encode (tl-make "rldp.query" :query-id (coerce query-id 'tl-octets) :max-answer-size max-answer-size
                                                   :timeout (+ (unix-now) (ceiling timeout)) :data (coerce data 'tl-octets)))))
      (setf (gethash query-id (rldpc-pending conn)) pending)
      (%rldp-start-transfer conn transfer-id query now deadline)
      pending)))

(defun rldp-pending-answer (pending) (rpend-answer pending))

(defun rldp-query-cancel (conn pending)
  "Forget PENDING and stop sending its query."
  (sb-thread:with-mutex ((rldpc-lock conn))
    (remhash (rpend-query-id pending) (rldpc-pending conn))
    (remhash (rpend-transfer-id pending) (rldpc-outbound conn))
    (remhash (rpend-answer-id pending) (rldpc-inbound conn))))

(defun rldp-query (conn data &key (timeout 5) (max-answer-size 1048576))
  "Run the query DATA over CONN and return the answer octets; signals RLDP-TIMEOUT after TIMEOUT seconds.  The calling thread
drives the connection's clock while it waits; incoming messages are fed by RLDP-RECEIVE from the transport's thread."
  (let* ((start (rldp-clock)) (deadline (+ start timeout))
         (pending (rldp-query-start conn data :timeout timeout :max-answer-size max-answer-size :now start)))
    (unwind-protect
         (loop
           (let* ((now (rldp-clock)) (left (- deadline now)))
             (when (rldp-pending-answer pending) (return (rldp-pending-answer pending)))
             (when (<= left 0)
               (error 'rldp-timeout :format-control "RLDP query: no answer in ~As" :format-arguments (list timeout)))
             (let ((wake (rldp-tick conn now)))
               (when (sb-thread:wait-on-semaphore (rpend-semaphore pending)
                                                  :timeout (max 0.0005d0 (min left 0.05d0 (if wake (- wake now) 0.05d0))))
                 (return (rldp-pending-answer pending))))))
      (rldp-query-cancel conn pending))))
