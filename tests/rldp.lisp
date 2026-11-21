;;;; tests/rldp.lisp -- RLDP2 (src/rldp.lisp) over a simulated lossy network.
;;;;
;;;; Two connections talk through a deterministic network with a simulated clock: every message may be lost, duplicated, delayed
;;;; and thereby reordered (a seeded random state).  One connection is a client, the other answers queries like a node (the
;;;; same code with ON-QUERY set), so a query goes out as a RaptorQ-coded transfer, the answer comes back as one, up to 5 parts
;;;; of 2,000,000 octets.  The wire formats and the receiver's rules come from the node's sources (see src/rldp.lisp); what this
;;;; file cannot show is that real nodes accept our queries: the gate probe on the real network does that.

(in-package :cl-ton/test)

(defstruct (%rldp-t-net (:conc-name %rtn-))
  (now 0d0) (queue '()) (rng (sb-ext:seed-random-state 1))
  (loss 0.0) (dup 0.0) (latency 0.02d0) (jitter 0.01d0) (sent 0) (dropped 0))

(defun %rldp-t-wire (net deliver)
  "A SEND function for a connection: messages to DELIVER (a function of octets and the arrival time) through NET's faults."
  (lambda (octets)
    (incf (%rtn-sent net))
    (if (< (random 1.0 (%rtn-rng net)) (%rtn-loss net))
        (incf (%rtn-dropped net))
        (dotimes (copy (if (< (random 1.0 (%rtn-rng net)) (%rtn-dup net)) 2 1))
          (push (cons (+ (%rtn-now net) (%rtn-latency net) (if (plusp (%rtn-jitter net)) (random (%rtn-jitter net) (%rtn-rng net)) 0d0))
                      (lambda (at) (funcall deliver octets at)))
                (%rtn-queue net))))))

(defun %rldp-t-run (net conns done-p &key (limit 60d0))
  "Advance the simulated clock event by event until DONE-P, the time LIMIT, or nothing is left to happen (returns NIL then)."
  (loop
    (when (funcall done-p) (return t))
    (when (> (%rtn-now net) limit) (return nil))
    (let* ((wakes (loop for c in conns for w = (cl-ton::rldp-tick c (%rtn-now net)) when w collect w))
           (next (reduce #'min (append (mapcar #'car (%rtn-queue net)) wakes) :initial-value most-positive-double-float)))
      (when (= next most-positive-double-float) (return (funcall done-p)))
      (setf (%rtn-now net) (max (%rtn-now net) (min next (+ (%rtn-now net) 5d0))))
      (let ((due (stable-sort (reverse (remove-if-not (lambda (e) (<= (car e) (%rtn-now net))) (%rtn-queue net))) #'< :key #'car)))
        (setf (%rtn-queue net) (remove-if (lambda (e) (<= (car e) (%rtn-now net))) (%rtn-queue net)))
        (dolist (e due) (funcall (cdr e) (car e)))))))

(defun %rldp-t-pair (net answer-fn)
  "(VALUES CLIENT SERVER): connections wired through NET; the server answers (funcall ANSWER-FN query-data)."
  (let (client server)
    (setf client (cl-ton::make-rldp-connection (%rldp-t-wire net (lambda (m at) (cl-ton::rldp-receive server m :now at)))))
    (setf server (cl-ton::make-rldp-connection (%rldp-t-wire net (lambda (m at) (cl-ton::rldp-receive client m :now at)))
                                               :on-query answer-fn))
    (values client server)))

(defun %rldp-t-blob (size seed)
  (let ((v (make-array size :element-type '(unsigned-byte 8))))
    (dotimes (i size v) (setf (aref v i) (ldb (byte 8 0) (+ (* i 7) (ash i -5) seed))))))

(defun %rldp-t-exchange (&key (query-size 100) (answer-size 60) (loss 0.0) (dup 0.0) (jitter 0.01d0) (seed 1) (max-answer 1048576)
                           (limit 60d0))
  "Run one query/answer; (VALUES answer-ok-p net client pending)."
  (let* ((net (make-%rldp-t-net :loss loss :dup dup :jitter jitter :rng (sb-ext:seed-random-state seed)))
         (query (%rldp-t-blob query-size 3))
         (answer (%rldp-t-blob answer-size 9)))
    (multiple-value-bind (client server) (%rldp-t-pair net (lambda (data) (and (equalp data query) answer)))
      (let ((pending (cl-ton::rldp-query-start client query :timeout limit :max-answer-size max-answer :now 0d0)))
        (%rldp-t-run net (list client server) (lambda () (cl-ton::rldp-pending-answer pending)) :limit limit)
        (values (equalp (cl-ton::rldp-pending-answer pending) answer) net client pending)))))

(defun test-rldp ()
  ;; --- Ack (rldp2/Ack.cpp)
  (let ((ack (cl-ton::make-rldp-ack)))
    (check "ack: 1, 2, 3 are new (count 3, mask 7, max 3); a repeat of 2 is not"
           (and (cl-ton::%rldp-ack-got ack 1) (cl-ton::%rldp-ack-got ack 2) (cl-ton::%rldp-ack-got ack 3)
                (not (cl-ton::%rldp-ack-got ack 2))
                (= (cl-ton::rack-count ack) 3) (= (cl-ton::rack-mask ack) 7) (= (cl-ton::rack-max-seqno ack) 3)))
    (check "ack: a jump of 40 clears the window, the old packet 3 is outside it (not new), 39..40 are new"
           (and (cl-ton::%rldp-ack-got ack 40) (not (cl-ton::%rldp-ack-got ack 3)) (cl-ton::%rldp-ack-got ack 39)
                (= (cl-ton::rack-mask ack) 3) (= (cl-ton::rack-max-seqno ack) 40) (= (cl-ton::rack-count ack) 5))))
  (check "the 32-bit mask goes over the wire as a signed int" (and (= -1 (cl-ton::%rldp-s32 #xFFFFFFFF)) (= 5 (cl-ton::%rldp-s32 5))))
  ;; --- queries over a perfect network
  (multiple-value-bind (ok net client) (%rldp-t-exchange :answer-size 20000 :jitter 0d0)   ; no reordering: the source symbols come first
    (declare (ignore net))
    (let ((stats (cl-ton::rldp-stats client)))
      (check "rldp stats: a 20,000-octet answer over a perfect, ordered network: 1 part, no repair, no duplicates"
             (and ok (= 1 (getf stats :parts)) (zerop (getf stats :repaired)) (zerop (getf stats :duplicates))))))
  (multiple-value-bind (ok net client) (%rldp-t-exchange :answer-size 100000 :loss 0.2 :dup 0.5 :seed 4)
    (declare (ignore net))
    (let ((stats (cl-ton::rldp-stats client)))
      (check "rldp stats: with 20% loss and 50% duplicates the answer needed repair and duplicates were dropped"
             (and ok (= 1 (getf stats :parts)) (= 1 (getf stats :repaired)) (plusp (getf stats :duplicates))
                  (>= (getf stats :packets) 131)))))
  (multiple-value-bind (ok net) (%rldp-t-exchange)
    (check "rldp: a small query and answer over a perfect network" ok)
    (check "rldp: ...in a handful of messages (query burst, confirms, answer burst, complete)" (< (%rtn-sent net) 30)))
  (check "rldp: an empty-looking one-octet query and a 1-octet answer"
         (%rldp-t-exchange :query-size 1 :answer-size 1))
  ;; --- loss, duplication, reordering
  (loop for loss in '(0.1 0.3 0.5)
        do (check (format nil "rldp: small query and answer with ~D% of the messages lost (3 seeds)" (round (* 100 loss)))
                  (loop for seed from 1 to 3 always (%rldp-t-exchange :loss loss :seed seed))))
  (check "rldp: a 20,000-octet answer with 10% loss, 50% duplicates and 200 ms of jitter (reordering)"
         (%rldp-t-exchange :answer-size 20000 :loss 0.1 :dup 0.5 :jitter 0.2d0))
  (check "rldp: a 600-octet query (one symbol would not hold the rldp.query header) and a 100,000-octet answer, 20% loss"
         (%rldp-t-exchange :query-size 600 :answer-size 100000 :loss 0.2))
  (check "rldp: a 5,000-octet QUERY (client-side transfer of 7 symbols) with 30% loss"
         (%rldp-t-exchange :query-size 5000 :answer-size 40 :loss 0.3))
  (check "rldp: an answer that nearly fills one part (1,990,000 octets, K=2591) with 10% loss"
         (%rldp-t-exchange :answer-size 1990000 :loss 0.1 :limit 120d0 :max-answer 2000000))
  (check "rldp: a 4,200,000-octet answer (three parts: 2,000,000 + 2,000,000 + 200,000) with 5% loss"
         (%rldp-t-exchange :answer-size 4200000 :loss 0.05 :limit 180d0 :max-answer 5000000))
  ;; --- the receiver's rules
  (multiple-value-bind (ok net client pending) (%rldp-t-exchange :answer-size 20000)
    (declare (ignore net))
    (check "rldp: the answer arrived and nothing is left behind on the client except the finished-transfer memory"
           (and ok (zerop (hash-table-count (cl-ton::rldpc-inbound client)))
                (plusp (hash-table-count (cl-ton::rldpc-completed client)))))
    (let ((sent '()) (answer-id (cl-ton::rpend-answer-id pending)))
      (let ((probe (cl-ton::make-rldp-connection (lambda (m) (push m sent)))))
        (setf (gethash answer-id (cl-ton::rldpc-completed probe)) 1d9)
        (cl-ton::rldp-receive probe
                              (cl-ton::tl-encode
                               (cl-ton::tl-make "rldp2.messagePart" :transfer-id (coerce answer-id 'cl-ton::tl-octets)
                                                                    :fec-type (cl-ton::tl-make "fec.raptorQ" :data-size 20000 :symbol-size 768 :symbols-count 27)
                                                                    :part 0 :total-size 20000 :seqno 3
                                                                    :data (make-array 768 :element-type '(unsigned-byte 8) :initial-element 0)))
                              :now 1d0)
        (check "rldp: a packet of a finished transfer is answered with rldp2.complete"
               (and (= 1 (length sent))
                    (let ((m (cl-ton::tl-decode (first sent))))
                      (and (cl-ton::tl-is m "rldp2.complete") (equalp (cl-ton::as-octets (cl-ton::tl-get m :transfer-id)) answer-id)
                           (= 0 (cl-ton::tl-get m :part)))))))))
  (let* ((sent '()) (conn (cl-ton::make-rldp-connection (lambda (m) (push m sent)))))
    (flet ((part (&key (id (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7)) (symbol-size 768) (data-size 20000)
                    (symbols-count 27) (index 0) (total 20000) (data-length 768))
             (cl-ton::tl-encode
              (cl-ton::tl-make "rldp2.messagePart" :transfer-id (coerce id 'cl-ton::tl-octets)
                                                   :fec-type (cl-ton::tl-make "fec.raptorQ" :data-size data-size :symbol-size symbol-size
                                                                                            :symbols-count symbols-count)
                                                   :part index :total-size total :seqno 0
                                                   :data (make-array data-length :element-type '(unsigned-byte 8) :initial-element 1)))))
      (cl-ton::rldp-receive conn (part) :now 0d0)
      (check "rldp: a client ignores a transfer it did not ask for (no state, no reply)"
             (and (zerop (hash-table-count (cl-ton::rldpc-inbound conn))) (null sent)))
      (cl-ton::rldp-receive conn (map 'vector #'identity #(1 2 3 4 5)) :now 0d0)
      (cl-ton::rldp-receive conn (make-array 0 :element-type '(unsigned-byte 8)) :now 0d0)
      (check "rldp: garbage and empty messages are ignored" (null sent))
      ;; a pending query expects the answer transfer; bad parts of it are dropped
      (let* ((pending (cl-ton::rldp-query-start conn (make-array 10 :element-type '(unsigned-byte 8) :initial-element 1) :now 0d0))
             (id (cl-ton::rpend-answer-id pending)))
        (setf sent '())
        (dolist (bad (list (part :id id :symbol-size 512) (part :id id :data-size 19999) (part :id id :symbols-count 26)
                           (part :id id :index 1) (part :id id :data-length 700) (part :id id :total 0 :data-size 20000)))
          (cl-ton::rldp-receive conn bad :now 0d0))
        (check "rldp: parts with a wrong symbol size, part size, symbol count, part number or data length are dropped"
               (and (zerop (hash-table-count (cl-ton::rldpc-inbound conn))) (null sent)))
        (cl-ton::rldp-receive conn (part :id id :data-size 20000 :symbols-count 27) :now 0d0)
        (check "rldp: a good first part of the expected answer opens the transfer"
               (= 1 (hash-table-count (cl-ton::rldpc-inbound conn))))
        (cl-ton::rldp-receive conn (part :id id :data-size 20000 :symbols-count 27) :now 0d0)
        (check "rldp: the same symbol again (a duplicate) is counted once"
               (let ((part (loop for p being the hash-values of (cl-ton::rin-parts (first (loop for v being the hash-values of (cl-ton::rldpc-inbound conn) collect v)))
                                 return p)))
                 (= 1 (cl-ton::rack-count (cl-ton::rip-ack part)))))
        (cl-ton::rldp-tick conn 0.0005d0)
        (check "rldp: no confirm before the ack delay (1 ms)" (null (remove-if-not (lambda (m) (cl-ton::tl-is (cl-ton::tl-decode m) "rldp2.confirm")) sent)))
        (cl-ton::rldp-tick conn 0.0011d0)
        (check "rldp: a confirm after it, with count 1 and the packet numbered from 1"
               (let ((m (find-if (lambda (m) (cl-ton::tl-is (cl-ton::tl-decode m) "rldp2.confirm")) sent)))
                 (and m (let ((c (cl-ton::tl-decode m)))
                          (and (= 1 (cl-ton::tl-get c :received-count)) (= 1 (cl-ton::tl-get c :max-seqno))
                               (= 1 (cl-ton::tl-get c :received-mask)))))))
        (cl-ton::rldp-tick conn 20d0)
        (check "rldp: an unfinished transfer is dropped after its deadline" (zerop (hash-table-count (cl-ton::rldpc-inbound conn)))))))
  (let ((net (make-%rldp-t-net)))
    (check "rldp: an answer larger than max_answer_size is never delivered (the query just times out)"
           (let* ((answer (%rldp-t-blob 20000 9)))
             (multiple-value-bind (client server) (%rldp-t-pair net (lambda (data) (declare (ignore data)) answer))
               (let ((pending (cl-ton::rldp-query-start client (%rldp-t-blob 20 1) :timeout 5 :max-answer-size 1000 :now 0d0)))
                 (%rldp-t-run net (list client server) (lambda () (cl-ton::rldp-pending-answer pending)) :limit 6d0)
                 (null (cl-ton::rldp-pending-answer pending)))))))
  ;; --- the blocking query on the real clock, through a threaded loopback
  (let (client server (lock (sb-thread:make-mutex)))
    (flet ((later (target) (lambda (m) (sb-thread:make-thread (lambda () (sb-thread:with-mutex (lock) (cl-ton::rldp-receive (funcall target) m)))))))
      (setf client (cl-ton::make-rldp-connection (later (lambda () server))))
      (setf server (cl-ton::make-rldp-connection (later (lambda () client)) :on-query (lambda (data) (reverse data)))))
    (let ((ticker (sb-thread:make-thread (lambda () (loop repeat 400 do (cl-ton::rldp-tick server) (sleep 0.005))))))
      (check "rldp-query: the blocking call on the real clock returns the answer (a reversed query)"
             (equalp (cl-ton::rldp-query client (coerce #(1 2 3 4 5) '(vector (unsigned-byte 8))) :timeout 4)
                     (coerce #(5 4 3 2 1) '(vector (unsigned-byte 8)))))
      (sb-thread:join-thread ticker :default nil)))
  (check "rldp-query: with nobody answering it signals RLDP-TIMEOUT after the timeout"
         (handler-case (progn (cl-ton::rldp-query (cl-ton::make-rldp-connection (lambda (m) (declare (ignore m)))) #(1 2 3) :timeout 0.3) nil)
           (cl-ton::rldp-timeout () t))))
