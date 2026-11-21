;;;; tests/overlay-query.lisp -- the ADNL custom-message hook and OVERLAY-QUERY (src/overlay-query.lisp) over real UDP sockets on
;;;; loopback, against a node-like fake peer: the same RLDP2 code in server mode behind an ADNL node that checks the
;;;; overlay.query framing and answers tonNode.* functions.  Whether real nodes agree is for the gate probe on the real network.

(in-package :cl-ton/test)

(defparameter +oq-t-zero+ (cl-ton::base64-decode "XplPz01CXAps5qeSWUtxcyBfdAo5zVb1N979KLSKD24="))

(defstruct (%oq-t-node (:conc-name %oqn-)) adnl overlay-id (conns (make-hash-table :test 'equalp)) (lock (sb-thread:make-mutex))
  (seen '()) (loss 0.0) (rng (sb-ext:seed-random-state 5)) ticker (running t) responder)

(defun %oq-t-answer (node data)
  "What the fake node answers to the framed query DATA; NIL (silence) when the framing is wrong."
  (multiple-value-bind (frame rest) (cl-ton::tl-decode-prefix data)
    (when (and (cl-ton::tl-is frame "overlay.query")
               (equalp (cl-ton::as-octets (cl-ton::tl-get frame :overlay)) (%oqn-overlay-id node)))
      (let ((function (cl-ton::tl-decode rest)))
        (sb-thread:with-mutex ((%oqn-lock node)) (push (cl-ton::tl-obj-name function) (%oqn-seen node)))
        (cond ((%oqn-responder node) (funcall (%oqn-responder node) function))
              ((cl-ton::tl-is function "tonNode.getCapabilities")
               (cl-ton::tl-encode (cl-ton::tl-make "tonNode.capabilities" :version-major 3 :version-minor 3 :flags 0)))
              ((cl-ton::tl-is function "tonNode.downloadBlock")
               (%rldp-t-blob 200000 77))
              (t nil))))))

(defun %oq-t-start-node (&key (loss 0.0) responder)
  "A fake full node: an ADNL UDP node whose custom messages go to per-peer RLDP connections in server mode, and whose plain
ADNL queries are answered like the RLDP ones; a ticker thread drives the RLDP clocks."
  (let* ((node (make-%oq-t-node :loss loss :responder responder :overlay-id (cl-ton::overlay-id-of-shard -1 -9223372036854775808 +oq-t-zero+)))
         (adnl (cl-ton::adnl-udp-start
                :host "127.0.0.1"
                :handler (lambda (query public) (declare (ignore public)) (let ((a (%oq-t-answer node query))) (and a (< (length a) 4000) a)))
                :custom-handler (lambda (data public)
                                  (let ((conn (sb-thread:with-mutex ((%oqn-lock node))
                                                (or (gethash (cl-ton::adnl-short-id public) (%oqn-conns node))
                                                    (setf (gethash (cl-ton::adnl-short-id public) (%oqn-conns node))
                                                          (cl-ton::make-rldp-connection
                                                           (lambda (m)
                                                             (unless (< (random 1.0 (%oqn-rng node)) (%oqn-loss node))
                                                               (let ((peer (cl-ton::adnl-udp-peer-of (%oqn-adnl node) public)))
                                                                 (cl-ton::adnl-udp-send-custom
                                                                  (%oqn-adnl node) (format nil "~{~D~^.~}" (coerce (cl-ton::adnl-udp-peer-host peer) 'list))
                                                                  (cl-ton::adnl-udp-peer-port peer) public m))))
                                                           :on-query (lambda (d) (%oq-t-answer node d))))))))
                                    (cl-ton::rldp-receive conn data))))))
    (setf (%oqn-adnl node) adnl)
    (setf (%oqn-ticker node)
          (sb-thread:make-thread (lambda ()
                                   (loop while (%oqn-running node)
                                         do (dolist (c (sb-thread:with-mutex ((%oqn-lock node)) (loop for v being the hash-values of (%oqn-conns node) collect v)))
                                              (cl-ton::rldp-tick c))
                                            (sleep 0.003)))))
    node))

(defun %oq-t-stop-node (node)
  (setf (%oqn-running node) nil)
  (sb-thread:join-thread (%oqn-ticker node) :default nil)
  (cl-ton::adnl-udp-stop (%oqn-adnl node)))

(defun test-overlay-query ()
  ;; --- the overlay id (the value the mainnet nodes answered to in the real run of 2026-11-04)
  (check "overlay id: masterchain id of the mainnet zero state = fc061ba1...db3b (the nodes answered to it)"
         (equalp (cl-ton::overlay-id-of-shard -1 -9223372036854775808 +oq-t-zero+)
                 (cl-ton::hex->octets "fc061ba11e1d7ba92dc6eb25ba79174a5ea4b11ea6299f9cd80df4214f1ddb3b")))
  (check "overlay id: the basechain id differs (12b8a83f...)"
         (equalp (cl-ton::overlay-id-of-shard 0 -9223372036854775808 +oq-t-zero+)
                 (cl-ton::hex->octets "12b8a83f098e15ea47fe76d0b0df0986ff6dda1980796b084b0d2a68b2558649")))
  (check "overlay query framing: boxed overlay.query then the boxed function"
         (multiple-value-bind (frame rest)
             (cl-ton::tl-decode-prefix (cl-ton::overlay-query-bytes (make-array 32 :element-type '(unsigned-byte 8) :initial-element 9)
                                                                    (cl-ton::tl-make "tonNode.getCapabilities")))
           (and (cl-ton::tl-is frame "overlay.query") (cl-ton::tl-is (cl-ton::tl-decode rest) "tonNode.getCapabilities"))))
  ;; --- the custom message hook
  (let* ((got '()) (lock (sb-thread:make-mutex))
         (b (cl-ton::adnl-udp-start :host "127.0.0.1"
                                    :custom-handler (lambda (data public)
                                                      (sb-thread:with-mutex (lock) (push (cons data public) got)))))
         (a (cl-ton::adnl-udp-start :host "127.0.0.1"))
         (quiet (cl-ton::adnl-udp-start :host "127.0.0.1")))
    (unwind-protect
         (flet ((wait (n) (loop repeat 200 until (>= (length got) n) do (sleep 0.01))))
           (cl-ton::adnl-udp-send-custom a "127.0.0.1" (cl-ton::adnl-udp-port b) (cl-ton::keypair-public (cl-ton::adnl-udp-keypair b))
                                         (%rldp-t-blob 100 1))
           (wait 1)
           (check "custom message: a small one arrives with the sender's public key"
                  (and (= 1 (length got)) (equalp (car (first got)) (%rldp-t-blob 100 1))
                       (equalp (cdr (first got)) (cl-ton::keypair-public (cl-ton::adnl-udp-keypair a)))))
           (cl-ton::adnl-udp-send-custom a "127.0.0.1" (cl-ton::adnl-udp-port b) (cl-ton::keypair-public (cl-ton::adnl-udp-keypair b))
                                         (%rldp-t-blob 3000 2))
           (wait 2)
           (check "custom message: a 3000-octet one (several datagrams) arrives whole, once"
                  (and (= 2 (length got)) (equalp (car (first got)) (%rldp-t-blob 3000 2))))
           (cl-ton::adnl-udp-send-custom a "127.0.0.1" (cl-ton::adnl-udp-port quiet) (cl-ton::keypair-public (cl-ton::adnl-udp-keypair quiet))
                                         (%rldp-t-blob 10 3))
           (sleep 0.1)
           (check "custom message: a node without a custom handler just ignores it" (= 0 (cl-ton::adnl-udp-dropped quiet))))
      (mapc #'cl-ton::adnl-udp-stop (list a b quiet))))
  ;; --- OVERLAY-QUERY against the fake node
  (let* ((node (%oq-t-start-node))
         (client (cl-ton::make-overlay-client (cl-ton::adnl-udp-start :host "127.0.0.1")))
         (port (cl-ton::adnl-udp-port (%oqn-adnl node)))
         (public (cl-ton::keypair-public (cl-ton::adnl-udp-keypair (%oqn-adnl node)))))
    (unwind-protect
         (flet ((q (function &rest keys)
                  (apply #'cl-ton::overlay-query client "127.0.0.1" port public (%oqn-overlay-id node) function keys)))
           (let ((answer (q (cl-ton::tl-make "tonNode.getCapabilities"))))
             (check "overlay-query over RLDP2: tonNode.getCapabilities answered with the capabilities (small answer)"
                    (let ((o (cl-ton::tl-decode answer)))
                      (and (cl-ton::tl-is o "tonNode.capabilities") (= 3 (cl-ton::tl-get o :version-major))))))
           (check "overlay-query over plain ADNL: the same, one datagram exchange"
                  (cl-ton::tl-is (cl-ton::tl-decode (q (cl-ton::tl-make "tonNode.getCapabilities") :transport :adnl)) "tonNode.capabilities"))
           (check "overlay-query: the function may be given as boxed octets"
                  (cl-ton::tl-is (cl-ton::tl-decode (q (cl-ton::tl-encode (cl-ton::tl-make "tonNode.getCapabilities")))) "tonNode.capabilities"))
           (let ((block-id (cl-ton::tl-make "tonNode.blockIdExt" :workchain -1 :shard -9223372036854775808 :seqno 5
                                                                 :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 1)
                                                                 :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 2))))
             (check "overlay-query over RLDP2: a 200,000-octet answer (about 261 symbols over real UDP) arrives whole"
                    (equalp (q (cl-ton::tl-make "tonNode.downloadBlock" :block block-id)) (%rldp-t-blob 200000 77)))
             (check "overlay-query: the fake node saw the framed functions"
                    (and (member "tonNode.getCapabilities" (%oqn-seen node) :test #'string=)
                         (member "tonNode.downloadBlock" (%oqn-seen node) :test #'string=)))
             (setf (%oqn-loss node) 0.2)
             (check "overlay-query over RLDP2: the same 200,000-octet answer while the node's packets are 20% lost"
                    (equalp (q (cl-ton::tl-make "tonNode.downloadBlock" :block block-id) :timeout 20) (%rldp-t-blob 200000 77)))
             (setf (%oqn-loss node) 0.0)
             (check "overlay-query: an answer bigger than max-answer-size never arrives (timeout)"
                    (handler-case (progn (q (cl-ton::tl-make "tonNode.downloadBlock" :block block-id) :max-answer-size 1000 :timeout 1.5) nil)
                      (cl-ton::rldp-timeout () t))))
           (check "overlay-query: an overlay the node does not serve gets no answer (RLDP2 timeout, ADNL timeout)"
                  (let ((other (make-array 32 :element-type '(unsigned-byte 8) :initial-element 3)))
                    (and (handler-case (progn (cl-ton::overlay-query client "127.0.0.1" port public other (cl-ton::tl-make "tonNode.getCapabilities") :timeout 0.6) nil)
                           (cl-ton::rldp-timeout () t))
                         (handler-case (progn (cl-ton::overlay-query client "127.0.0.1" port public other (cl-ton::tl-make "tonNode.getCapabilities")
                                                                     :transport :adnl :timeout 0.6)
                                              nil)
                           (cl-ton::adnl-udp-timeout () t))))))
      (%oq-t-stop-node node)
      (cl-ton::adnl-udp-stop (cl-ton::ocl-node client)))))
;;; --- the tonNode client (src/overlay-query.lisp, "the tonNode client"): a pool of fake peers serving the REAL captured block, proofs and
;;; key block (fixtures/real/node-*), some of them silent, lying, lagging or not holding the block -------------------------------------

(defun %tn-t-octets (string) (coerce (map 'vector #'char-code string) '(simple-array (unsigned-byte 8) (*))))

(defun %tn-t-id (seqno)
  "A synthetic masterchain block id (the chain the fake peers walk), hashes derived from the seqno."
  (cl-ton::tl-make "tonNode.blockIdExt" :workchain -1 :shard (cl-ton::%signed64 #x8000000000000000) :seqno seqno
                                        :root-hash (cl-ton::sha256 (%tn-t-octets (format nil "r~D" seqno)))
                                        :file-hash (cl-ton::sha256 (%tn-t-octets (format nil "f~D" seqno)))))

(defun %tn-t-lz4-literals (octets)
  "An LZ4 block that holds OCTETS as literals only (valid LZ4; no compressor needed in a test)."
  (let ((n (length octets)) (out '()))
    (if (< n 15)
        (push (ash n 4) out)
        (progn (push (ash 15 4) out)
               (let ((rest (- n 15)))
                 (loop while (>= rest 255) do (push 255 out) (decf rest 255))
                 (push rest out))))
    (coerce (append (reverse out) (coerce octets 'list)) '(simple-array (unsigned-byte 8) (*)))))

(defun %tn-t-responder (world &key behind lie lacks silent proof-gate next-full single-full downloads)
  "The answers of a fake peer.  WORLD = plist of :head-id :head-proof :block-id :block :key-id :key-block :key-proof.  BEHIND: the
last masterchain seqno the peer knows; LIE: block and proof octets with a flipped octet; LACKS: says notFound to prepareBlock;
SILENT: never answers; NEXT-FULL: a function of the world giving the DataFull the peer sends for the masterchain block after the world's one (NIL = none); SINGLE-FULL: the same for downloadNextBlockFull; DOWNLOADS: a cons whose car counts the downloadBlock queries; PROOF-GATE: a cons whose car must be true before the peer answers a block proof (before it says nothing, like
a node that has not got the proof yet)."
  (lambda (function)
    (flet ((bad (octets) (if lie (let ((c (copy-seq octets))) (setf (aref c (floor (length c) 2)) (logxor (aref c (floor (length c) 2)) 1)) c) octets))
           (seqno (f) (cl-ton::tl-get (cl-ton::tl-get f :block) :seqno)))
      (cond (silent nil)
            ((cl-ton::tl-is function "tonNode.prepareBlock")
             (cl-ton::tl-encode (cl-ton::tl-make (if lacks "tonNode.notFound" "tonNode.prepared"))))
            ((and next-full (cl-ton::tl-is function "tonNode.downloadNextBlocksFull"))
             (cl-ton::tl-encode
              (cl-ton::tl-make "tonNode.nextBlocksFull"
                               :blocks (let ((d (and (= (cl-ton::tl-get (cl-ton::tl-get function :prev-block) :seqno) (1- (cl-ton::tl-get (getf world :block-id) :seqno)))
                                                     (funcall next-full world))))
                                         (if d (vector d) (vector))))))
            ((and single-full (cl-ton::tl-is function "tonNode.downloadNextBlockFull"))
             (cl-ton::tl-encode (if (= (cl-ton::tl-get (cl-ton::tl-get function :prev-block) :seqno) (1- (cl-ton::tl-get (getf world :block-id) :seqno)))
                                    (funcall single-full world)
                                    (cl-ton::tl-make "tonNode.dataFullEmpty"))))
            ((cl-ton::tl-is function "tonNode.downloadBlock")
             (let ((s (seqno function)))
               (when downloads (incf (car downloads)))
               (cond ((= s (cl-ton::tl-get (getf world :block-id) :seqno)) (bad (getf world :block)))
                     ((= s (cl-ton::tl-get (getf world :shard-id) :seqno)) (bad (getf world :shard-block)))
                     ((= s (cl-ton::tl-get (getf world :key-id) :seqno)) (bad (getf world :key-block)))
                     ;; a block the peer does not have: a short answer that is no block file (a real node says so too)
                     (t (cl-ton::tl-encode (cl-ton::tl-make "tonNode.notFound"))))))
            ((and proof-gate (not (car proof-gate)) (cl-ton::tl-is function "tonNode.downloadBlockProof")) nil)
            ((or (cl-ton::tl-is function "tonNode.downloadBlockProof") (cl-ton::tl-is function "tonNode.downloadKeyBlockProof"))
             (let ((s (seqno function)))
               (cond ((= s (cl-ton::tl-get (getf world :head-id) :seqno)) (bad (getf world :head-proof)))
                     ((= s (cl-ton::tl-get (getf world :key-id) :seqno)) (bad (getf world :key-proof)))
                     ((= s (cl-ton::tl-get (getf world :block-id) :seqno)) (bad (getf world :block-proof))))))
            ((cl-ton::tl-is function "tonNode.getNextBlockDescription")
             (let* ((p (cl-ton::tl-get (cl-ton::tl-get function :prev-block) :seqno)) (head (cl-ton::tl-get (getf world :head-id) :seqno)))
               (cl-ton::tl-encode
                (if (>= p (min head (or behind head)))
                    (cl-ton::tl-make "tonNode.blockDescriptionEmpty")
                    (cl-ton::tl-make "tonNode.blockDescription" :id (if (= (1+ p) head) (getf world :head-id) (%tn-t-id (1+ p))))))))
            ((cl-ton::tl-is function "tonNode.getNextKeyBlockIds")
             (cl-ton::tl-encode (cl-ton::tl-make "tonNode.keyBlocks" :blocks (vector (getf world :key-id)) :incomplete nil :error nil)))
            (t nil)))))

(defun test-tonnode-client ()
  (format t "tonNode client: pool, hedged queries, verified answers, head and key block~%")
  (let ((dir (%real-vector-dir)))
    (unless (probe-file (merge-pathnames "node-keyblock-103967771.boc" dir))
      (format t "  (no node fixtures in ~A)~%" dir)
      (return-from test-tonnode-client nil))
    (let* ((head-meta (getf (with-open-file (f (merge-pathnames "node-proof-104057524.sexp" dir)) (read f)) :block))
           (block-meta (with-open-file (f (merge-pathnames "node-block-103977810.sexp" dir)) (read f)))
           (mk (lambda (seqno meta) (cl-ton::tl-make "tonNode.blockIdExt" :workchain -1 :shard (cl-ton::%signed64 #x8000000000000000) :seqno seqno
                                                    :root-hash (cl-ton::hex->octets (getf meta :root-hash)) :file-hash (cl-ton::hex->octets (getf meta :file-hash)))))
           (key-octets (%read-octets (merge-pathnames "node-keyblock-103967771.boc" dir)))
           (key-cell (first (cl-ton::parse-boc key-octets)))
           (world (list :head-id (funcall mk 104057524 head-meta)
                        :head-proof (%read-octets (merge-pathnames "node-proof-104057524.boc" dir))
                        :block-id (funcall mk 103977810 block-meta) :block (%read-octets (merge-pathnames "node-block-103977810.boc" dir))
                        :block-proof (%read-octets (merge-pathnames "node-proof-103977810.boc" dir))
                        :shard-id (cl-ton::tl-make "tonNode.blockIdExt" :workchain 0 :shard (cl-ton::%signed64 #x8000000000000000) :seqno 108759255
                                                   :root-hash (cl-ton::hex->octets "97181f33686114cb86256c6e3a59ab668ed37c6dd1f0564121f08e3d4034845b")
                                                   :file-hash (cl-ton::hex->octets "1e721f965d301bde7c15d30639ad6e08ee7400f2100024c12004a6b2ead85e42"))
                        :shard-block (%read-octets (merge-pathnames "node-shardblock-108759255.boc" dir))
                        :key-id (cl-ton::tl-make "tonNode.blockIdExt" :workchain -1 :shard (cl-ton::%signed64 #x8000000000000000) :seqno 103967771
                                                 :root-hash (cl-ton::hex->octets (cl-ton::cell-hash-hex key-cell)) :file-hash (cl-ton::sha256 key-octets))
                        :key-block key-octets :key-proof (%read-octets (merge-pathnames "node-keyproof-103967771.boc" dir))))
           (gate (list nil))
           (dl (list 0))
           (plain-next (lambda (w) (cl-ton::tl-make "tonNode.dataFull" :id (getf w :block-id) :proof (getf w :block-proof) :block (getf w :block) :is-link nil)))
           (z-next (lambda (w) (cl-ton::tl-make "tonNode.dataFullCompressed" :id (getf w :block-id) :flags 0 :is-link nil
                                                :compressed (%tn-t-lz4-literals
                                                             (cl-ton::serialize-boc (list (first (cl-ton::parse-boc (getf w :block-proof)))
                                                                                          (first (cl-ton::parse-boc (getf w :block)))))))))
           (specs `((:a) (:silent :silent t) (:fresh :proof-gate ,gate) (:nextplain :next-full ,plain-next) (:nextz :next-full ,z-next) (:nextempty :next-full ,(lambda (w) (declare (ignore w)) nil)) (:nextsingle :next-full ,(lambda (w) (declare (ignore w)) nil) :single-full ,plain-next) (:count :downloads ,dl) (:liar :lie t) (:late :behind 104057510) (:lacks :lacks t)))
           (nodes (mapcar (lambda (sp) (cons (first sp) (%oq-t-start-node :responder (apply #'%tn-t-responder world (rest sp))))) specs))
           (client (cl-ton::make-overlay-client (cl-ton::adnl-udp-start :host "127.0.0.1")))
           (overlay (%oqn-overlay-id (cdr (first nodes)))))
      (unwind-protect
           (labels ((peers (&rest names)
                      (mapcar (lambda (n) (let ((node (cdr (assoc n nodes))))
                                            (list "127.0.0.1" (cl-ton::adnl-udp-port (%oqn-adnl node))
                                                  (cl-ton::keypair-public (cl-ton::adnl-udp-keypair (%oqn-adnl node))))))
                              names))
                    (pool (&rest names) (cl-ton::make-tonnode-pool client overlay (apply #'peers names)))
                    (peer-of (pool n) (nth (position n (mapcar #'car nodes)) (cl-ton::tnp-peers pool))))
             (declare (ignorable #'peer-of))
             ;; --- next block, follow
             (let* ((p (pool :a :silent)) (next (cl-ton::tonnode-next-block p (%tn-t-id 104057500))))
               (check "next block: a silent peer in the pool does not matter; the answer is the next synthetic id"
                      (and (= 104057501 (cl-ton::tl-get next :seqno)) (equalp (cl-ton::tl-get next :root-hash) (cl-ton::tl-get (%tn-t-id 104057501) :root-hash)))))
             (let ((p (pool :late :a)))
               (multiple-value-bind (id steps) (cl-ton::tonnode-follow p (%tn-t-id 104057500))
                 (check "follow: a lagging peer next to a good one; the walk reaches the real head 104057524 in 24 steps"
                        (and (= steps 24) (cl-ton::%same-block-id-p id (getf world :head-id))))))
             (check "follow: at the end of the chain every peer says empty -> :none"
                    (eq :none (cl-ton::tonnode-next-block (pool :a :late) (getf world :head-id))))
             ;; --- downloads
             (let* ((p (cl-ton::make-tonnode-pool client overlay (peers :silent :liar :a) :hedge 3)) ; all three asked at once: no luck needed
                    (data (cl-ton::tonnode-download-block p (getf world :block-id))))
               (check "download: a silent and a lying peer in the pool; the verified block of the honest one is returned"
                      (equalp data (getf world :block)))
               (sleep 0.6)                      ; the other workers finish after the winner has been returned
               (check "download: the liar was demoted (cool-down)"
                      (> (cl-ton::tn-peer-until (second (cl-ton::tnp-peers p))) (cl-ton::%tn-now))))
             ;; --- staggered hedging (fix 106): a silent peer costs STAGGER seconds, not a whole timeout
             (let* ((p (cl-ton::make-tonnode-pool client overlay (peers :silent :silent :a) :hedge 1 :stagger 0.5))
                    (t0 (get-internal-real-time)) (data (cl-ton::tonnode-download-block p (getf world :block-id) :timeout 6))
                    (secs (/ (- (get-internal-real-time) t0) internal-time-units-per-second 1.0)))
               (check "stagger: two silent peers asked first, the third (honest) joins after 0.5 s steps: the block arrives in < 4 s, not after 6 s timeouts"
                      (and (equalp data (getf world :block)) (< secs 4))))
             (let* ((p (cl-ton::make-tonnode-pool client overlay (peers :silent :silent) :hedge 1 :stagger 0.5))
                    (t0 (get-internal-real-time)))
               (check "stagger: only silent peers -> TONNODE-ERROR after the timeout (the overall limit), not earlier and not much later"
                      (and (handler-case (progn (cl-ton::tonnode-download-block p (getf world :block-id) :timeout 2) nil) (cl-ton::tonnode-error () t))
                           (let ((secs (/ (- (get-internal-real-time) t0) internal-time-units-per-second 1.0))) (< 1.5 secs 8)))))
             (check "stagger: NIL gives the old sequence of waves (the same answer)"
                    (let ((p (cl-ton::make-tonnode-pool client overlay (peers :a :silent) :hedge 2 :stagger nil)))
                      (equalp (cl-ton::tonnode-download-block p (getf world :block-id)) (getf world :block))))
             (check "download: only a liar -> TONNODE-ERROR (its block fails the hash check)"
                    (handler-case (progn (cl-ton::tonnode-download-block (pool :liar) (getf world :block-id) :timeout 3) nil)
                      (cl-ton::tonnode-error () t)))
             (let* ((p (pool :lacks :a)) (t0 (get-internal-real-time)) (data (cl-ton::tonnode-download-block p (getf world :block-id)))
                    (secs (/ (- (get-internal-real-time) t0) internal-time-units-per-second 1.0)))
               (check "download: a peer that says notFound to prepareBlock is skipped quickly and remembered"
                      (progn (sleep 0.4)
                             (and (equalp data (getf world :block)) (< secs 3)
                                  (gethash 103977810 (cl-ton::tn-peer-lacks (first (cl-ton::tnp-peers p))))))))
             (check "download: a block whose id has the wrong file hash is refused (no peer's data matches)"
                    (let ((wrong (cl-ton::tl-make "tonNode.blockIdExt" :workchain -1 :shard (cl-ton::tl-get (getf world :block-id) :shard) :seqno 103977810
                                                                      :root-hash (cl-ton::tl-get (getf world :block-id) :root-hash)
                                                                      :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 9))))
                      (handler-case (progn (cl-ton::tonnode-download-block (pool :a) wrong :timeout 3) nil) (cl-ton::tonnode-error () t))))
             ;; --- the verified head: the walk, then the proof of the last block against the key block's validator set
             (let ((p (pool :a :silent :late)))
               (multiple-value-bind (id info steps weight total count)
                   (cl-ton::tonnode-verified-head p (%tn-t-id 104057500) key-cell)
                 (check "verified head: walked 24 steps to 104057524, proof verified against the key block's set (68 signatures, > 2/3)"
                        (and (cl-ton::%same-block-id-p id (getf world :head-id)) (= 24 steps) (= 104057524 (getf info :seqno))
                             (= count 68) (> (* 3 weight) (* 2 total))))))
             (check "verified head: a peer that serves a damaged proof gives no head (TONNODE-ERROR) ..."
                    (handler-case (progn (cl-ton::tonnode-verified-head (pool :liar) (%tn-t-id 104057500) key-cell) nil)
                      (cl-ton::tonnode-error () t)))
             (check "...but next to an honest peer the damaged proof is skipped and the head still verifies"
                    (let ((p (pool :liar :a)))
                      (multiple-value-bind (id info) (cl-ton::tonnode-verified-head p (%tn-t-id 104057500) key-cell)
                        (and (cl-ton::%same-block-id-p id (getf world :head-id)) (= 104057524 (getf info :seqno))))))
             ;; --- the key block chain: the real next-key-block data cannot be tested until a second key block exists; what is checked is
             ;;     that a key block signed by a set other than the trusted block's current one is refused
             (check "advance key block: the key block's own proof was signed by the PREVIOUS set, so trusting it as its own predecessor is refused"
                    (handler-case (progn (cl-ton::tonnode-advance-key-block (pool :a) (getf world :key-id) key-cell) nil)
                      (cl-ton::tonnode-error () t)))
             (check "key block ids: the peers name the later key blocks (here the fake one) and the incomplete flag"
                    (multiple-value-bind (ids incomplete) (cl-ton::tonnode-next-key-block-ids (pool :a) (getf world :key-id))
                      (and (= 1 (length ids)) (not incomplete))))
             ;; --- a verified block, the shards a masterchain block names (fix 82)
             (multiple-value-bind (block info new-hash old-hash octets) (cl-ton::tonnode-verified-block (pool :silent :a) (getf world :block-id) :timeout 3)
               (check "verified block: the real masterchain block 103977810 is read with its hashes, header and the state hashes before and after"
                      (and (cl-ton::cell-p block) (= 103977810 (getf info :seqno)) (equalp octets (getf world :block))
                           (= 32 (length new-hash)) (= 32 (length old-hash)) (not (equalp new-hash old-hash))))
               (let ((shards (cl-ton::block-shard-descriptions block)))
                 (check "shard descriptions: the block names the basechain shard(s) with the ids of their newest blocks"
                        (and shards (find 0 shards :key (lambda (d) (getf d :workchain)))
                             (every (lambda (d) (and (= 32 (length (getf d :root-hash))) (= 32 (length (getf d :file-hash)))
                                                     (plusp (getf d :seqno)) (plusp (getf d :end-lt))))
                                    shards)))
                 (let* ((descr (find 0 shards :key (lambda (d) (getf d :workchain)))) (id (cl-ton::shard-descr-block-id descr)))
                   (check "shard block id: the blockIdExt of a description carries its workchain, signed shard, seqno and both hashes"
                          (and (= 0 (cl-ton::tl-get id :workchain)) (= (getf descr :seqno) (cl-ton::tl-get id :seqno))
                               (= (cl-ton::%signed64 (getf descr :shard)) (cl-ton::tl-get id :shard))
                               (equalp (getf descr :root-hash) (cl-ton::as-octets (cl-ton::tl-get id :root-hash)))
                               (equalp (getf descr :file-hash) (cl-ton::as-octets (cl-ton::tl-get id :file-hash))))))
                 (check "shard descriptions: a cell that is not a masterchain Block is refused (PROOF-ERROR)"
                        (handler-case (progn (cl-ton::block-shard-descriptions (svref (cl-ton::cell-refs block) 0)) nil)
                          (cl-ton::proof-error () t)))))
             (multiple-value-bind (block info new-hash shards weight total)
                 (cl-ton::tonnode-verified-masterchain-block (pool :silent :liar :a) (getf world :block-id) key-cell :timeout 4)
               (check "verified masterchain block: the real block 103977810 proven by the key block's validator set (> 2/3) and read, a liar and a silent peer skipped"
                      (and (cl-ton::cell-p block) (= 103977810 (getf info :seqno)) (= 32 (length new-hash))
                           (> (* 3 weight) (* 2 total)) shards (find 0 shards :key (lambda (d) (getf d :workchain))))))
             (check "verified masterchain block: only a liar in the pool gives no block (TONNODE-ERROR)"
                    (handler-case (progn (cl-ton::tonnode-verified-masterchain-block (pool :liar) (getf world :block-id) key-cell :timeout 3) nil)
                      (cl-ton::tonnode-error () t)))
             ;; --- the state roots: the key block 103967771 names the real shard block 108759255, which the fake peers serve
             (let* ((descrs (cl-ton::block-shard-descriptions key-cell)))
               (let ((states (cl-ton::tonnode-shard-states (pool :silent :liar :a) descrs :timeout 4)))
                 (check "shard states: the real basechain shard block named by the key block is fetched and its state hash read"
                        (and (= 1 (length states)) (= 108759255 (getf (getf (first states) :descr) :seqno)) (= 32 (length (getf (first states) :state-hash)))
                             (= 108759255 (getf (getf (first states) :info) :seqno))
                             (null (cl-ton::tonnode-shard-states (pool :a) descrs :workchain -1)))))
               (check "shard states: a description whose logical times differ from the block's is refused (PROOF-ERROR)"
                      (let ((forged (list (list* :end-lt 1 (let ((d (copy-list (first descrs)))) (remf d :end-lt) d)))))
                        (handler-case (progn (cl-ton::tonnode-shard-states (pool :a) forged :timeout 4) nil)
                          (cl-ton::proof-error () t))))
               (check "shard states: only a liar in the pool gives no block (TONNODE-ERROR)"
                      (handler-case (progn (cl-ton::tonnode-shard-states (pool :liar) descrs :timeout 3) nil)
                        (cl-ton::tonnode-error () t))))
             ;; --- following a shard (fix 85): the real shard block 108759255, its predecessor named inside it
             (let* ((tip (getf world :shard-id))
                    (chain (cl-ton::tonnode-shard-chain (pool :a) tip tip :timeout 3)))
               (check "shard chain: a tip that is already known gives no blocks and fetches nothing" (null chain)))
             (multiple-value-bind (block) (cl-ton::tonnode-verified-block (pool :a) (getf world :shard-id) :timeout 3)
               (let* ((prev (cl-ton::parse-block-links block (getf world :shard-id)))
                      (prev-id (cl-ton::shard-descr-block-id (first prev)))
                      (chain (cl-ton::tonnode-shard-chain (pool :silent :a) (getf world :shard-id) prev-id :timeout 3)))
                 (check "shard chain: the walk stops at the known predecessor named inside the block, returning the one new block with its links"
                        (and (= 1 (length chain)) (= 108759255 (getf (getf (first chain) :info) :seqno))
                             (= 1 (length (getf (first chain) :prev))) (= 108759254 (getf (first (getf (first chain) :prev)) :seqno))
                             (getf (first chain) :mc-ref) (= 32 (length (getf (first chain) :state-hash)))))
                 (let ((follow (cl-ton::tonnode-follow-shard (pool :a) (getf world :shard-id)
                                                             (list :id prev-id :state-hash (getf (first chain) :old-state-hash)) :timeout 3)))
                   (check "follow shard: the new block starts from the state the last known block ended in" (= 1 (length follow))))
                 (check "follow shard: a block that does not start from the last known state is refused (PROOF-ERROR)"
                        (handler-case (progn (cl-ton::tonnode-follow-shard (pool :a) (getf world :shard-id)
                                                                           (list :id prev-id :state-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7))
                                                                           :timeout 3)
                                             nil)
                          (cl-ton::proof-error () t)))
                 (check "shard chain: a predecessor no peer has is a TONNODE-ERROR (the walk went back to fetch it)"
                        (handler-case (progn (cl-ton::tonnode-shard-chain (pool :a) (getf world :shard-id) nil :timeout 2) nil)
                          (cl-ton::tonnode-error () t)))
                 (check "shard chain: more blocks than MAX-BLOCKS is a TONNODE-ERROR"
                        (handler-case (progn (cl-ton::tonnode-shard-chain (pool :a) (getf world :shard-id) nil :max-blocks 1 :timeout 2) nil)
                          (cl-ton::tonnode-error () t)))))
             (let* ((h (lambda (n) (make-array 32 :element-type '(unsigned-byte 8) :initial-element n)))
                    (id (lambda (seqno) (cl-ton::tl-make "tonNode.blockIdExt" :workchain 0 :shard (cl-ton::%signed64 #x8000000000000000) :seqno seqno
                                                                              :root-hash (funcall h seqno) :file-hash (funcall h 100))))
                    (prev-of (lambda (seqno) (list (list :workchain 0 :shard #x8000000000000000 :seqno seqno :root-hash (funcall h seqno) :file-hash (funcall h 100)))))
                    (b1 (list :id (funcall id 11) :prev (funcall prev-of 10) :old-state-hash (funcall h 50) :state-hash (funcall h 51)))
                    (b2 (list :id (funcall id 12) :prev (funcall prev-of 11) :old-state-hash (funcall h 51) :state-hash (funcall h 52)))
                    (b2-bad (list :id (funcall id 12) :prev (funcall prev-of 11) :old-state-hash (funcall h 99) :state-hash (funcall h 52))))
               (check "chain consistency: states that hang together pass, a break between two blocks is found"
                      (and (cl-ton::tonnode-chain-consistent-p (list b1 b2)) (not (cl-ton::tonnode-chain-consistent-p (list b1 b2-bad)))
                           (cl-ton::tonnode-chain-consistent-p (list b2-bad)))))
;; --- the follower (fix 86): the key block's shard description names the real shard block the fake peers serve
             (let* ((descrs (cl-ton::block-shard-descriptions key-cell))
                    (follower (cl-ton::make-tonnode-follower :key-block key-cell))
                    (block (cl-ton::tonnode-verified-block (pool :a) (getf world :shard-id) :timeout 3))
                    (prev-id (cl-ton::shard-descr-block-id (first (cl-ton::parse-block-links block (getf world :shard-id)))))
                    (old-state (nth-value 3 (cl-ton::tonnode-verified-block (pool :a) (getf world :shard-id) :timeout 3)))
                    (path (format nil "/tmp/follower-test-~D.sexp" (random 1000000))))
               (check "follower: the first look at a shard takes only its tip and the hash of its state"
                      (and (null (cl-ton::tonnode-follower-apply follower (pool :silent :a) descrs :timeout 4))
                           (= 1 (length (cl-ton::tfollower-shards follower)))
                           (= 32 (length (getf (first (cl-ton::tfollower-shards follower)) :state-hash)))))
               (check "follower: the same tip again changes nothing and fetches nothing"
                      (let ((before (copy-list (cl-ton::tfollower-shards follower))))
                        (and (null (cl-ton::tonnode-follower-apply follower (pool) descrs :timeout 1))
                             (equal before (cl-ton::tfollower-shards follower)))))
               (check "follower: what is kept in a file comes back (ids and state hashes)"
                      (unwind-protect
                           (progn (cl-ton::tonnode-follower-save follower path)
                                  (let ((other (cl-ton::make-tonnode-follower)))
                                    (and (cl-ton::tonnode-follower-restore other path)
                                         (cl-ton::%same-block-id-p (getf (first (cl-ton::tfollower-shards other)) :id) (getf world :shard-id))
                                         (equalp (getf (first (cl-ton::tfollower-shards other)) :state-hash)
                                                 (getf (first (cl-ton::tfollower-shards follower)) :state-hash)))))
                        (ignore-errors (delete-file path))))
               (check "follower: the key block and its id are kept with the state and come back (a newer key block is a better place to resume)"
                      (let ((kf (cl-ton::make-tonnode-follower :key-block key-cell :key-id (getf world :key-id))))
                        (unwind-protect
                             (progn (cl-ton::tonnode-follower-save kf path)
                                    (let ((other (cl-ton::make-tonnode-follower)))
                                      (and (cl-ton::tonnode-follower-restore other path)
                                           (cl-ton::%same-block-id-p (cl-ton::tfollower-key-id other) (getf world :key-id))
                                           (equalp (cl-ton::node-hash-at (cl-ton::tfollower-key-block other) 0) (cl-ton::node-hash-at key-cell 0)))))
                          (ignore-errors (delete-file path)) (ignore-errors (delete-file (format nil "~A.key.boc" path))))))
               (check "follower: a key block file that does not match the saved root hash is not taken"
                      (let ((kf (cl-ton::make-tonnode-follower :key-block key-cell :key-id (getf world :key-id))))
                        (unwind-protect
                             (progn (cl-ton::tonnode-follower-save kf path)
                                    (with-open-file (f (format nil "~A.key.boc" path) :direction :output :if-exists :supersede :element-type '(unsigned-byte 8))
                                      (write-sequence (cl-ton::serialize-boc (svref (cl-ton::cell-refs key-cell) 0)) f))
                                    (let ((other (cl-ton::make-tonnode-follower)))
                                      (and (cl-ton::tonnode-follower-restore other path)
                                           (null (cl-ton::tfollower-key-block other)) (null (cl-ton::tfollower-key-id other)))))
                          (ignore-errors (delete-file path)) (ignore-errors (delete-file (format nil "~A.key.boc" path))))))
               (check "follower: a missing or damaged file is not read and leaves the follower alone"
                      (let ((other (cl-ton::make-tonnode-follower)))
                        (and (not (cl-ton::tonnode-follower-restore other "/tmp/no-such-follower-file.sexp"))
                             (progn (with-open-file (f path :direction :output :if-exists :supersede) (write-string "(:follower 1 :shards (garbage" f))
                                    (not (cl-ton::tonnode-follower-restore other path)))
                             (null (cl-ton::tfollower-shards other))
                             (progn (ignore-errors (delete-file path)) t))))
               ;; the follower holds the PREDECESSOR (as if the last step had stopped one block earlier): the new tip is walked to it
               (let ((behind (cl-ton::make-tonnode-follower
                              :shards (list (list :id prev-id :state-hash old-state)))))
                 (let ((new (cl-ton::tonnode-follower-apply behind (pool :a) descrs :timeout 3)))
                   (check "follower: a shard held one block behind is brought up to the tip with the one block between"
                          (and (= 1 (length new)) (= 108759255 (getf (getf (first new) :info) :seqno))
                               (= 1 (length (cl-ton::tfollower-shards behind)))
                               (cl-ton::%same-block-id-p (getf (first (cl-ton::tfollower-shards behind)) :id) (getf world :shard-id))))))
               (let ((fresh (cl-ton::make-tonnode-follower :key-block key-cell)))
                 (check "follower step: the masterchain block is proven but its basechain tip is not served: TONNODE-ERROR and nothing is taken in"
                        (and (handler-case (progn (cl-ton::tonnode-follower-step fresh (pool :a) (pool :a) (getf world :block-id) :timeout 2) nil)
                               (cl-ton::tonnode-error () t))
                             (null (cl-ton::tfollower-mc-id fresh)) (null (cl-ton::tfollower-shards fresh)))))
               ;; --- the watchlist (Phase 5 hot path) on the real shard block 108759255: 12 accounts changed in it
               (multiple-value-bind (wblock winfo wnew) (cl-ton::tonnode-verified-block (pool :a) (getf world :shard-id) :timeout 3)
                 (declare (ignore winfo))
                 (let* ((changes (cl-ton::block-account-changes wblock))
                        (hit (getf (first changes) :account)) (hit2 (getf (second changes) :account))
                        (miss (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7))
                        (wl (cl-ton::make-tonnode-watchlist))
                        (blocks (list (list :id (getf world :shard-id) :block wblock :state-hash wnew))))
                   (cl-ton::tonnode-watch-add wl hit) (cl-ton::tonnode-watch-add wl (cl-ton::octets->hex miss))
                   (check "watchlist: an account put on the list is stale until it has a state"
                          (and (= 2 (length (cl-ton::tonnode-watch-stale wl))) (getf (cl-ton::tonnode-watch-get wl hit) :stale)
                               (null (cl-ton::tonnode-watch-get wl hit2))))
                   (let ((events (cl-ton::tonnode-watch-blocks wl blocks)) (entry (cl-ton::tonnode-watch-get wl hit)))
                     (check "watchlist: the block changed one watched account: one event, the entry is fresh and agrees with the AccountBlock"
                            (and (= 1 (length events)) (string= (getf (first events) :account) (cl-ton::octets->hex hit))
                                 (getf (first events) :exists) (not (getf entry :stale))
                                 (= (getf entry :last-trans-lt) (getf (first changes) :last-lt))
                                 (equalp (getf entry :last-trans-hash) (getf (first changes) :last-trans-hash))
                                 (equalp (getf entry :state-hash) wnew)
                                 (equal (cl-ton::tonnode-watch-stale wl) (list (cl-ton::octets->hex miss)))))
                     (check "watchlist: an account the block did not change stays as it was, and one never watched is not added"
                            (and (getf (cl-ton::tonnode-watch-get wl miss) :stale) (null (cl-ton::tonnode-watch-get wl hit2))))
                     (check "watchlist: a state read from an OLDER block of the same shard never replaces a newer one"
                            (let ((older (cl-ton::tl-make "tonNode.blockIdExt" :workchain 0 :shard (cl-ton::tl-get (getf world :shard-id) :shard)
                                                                                :seqno 108759254 :root-hash (cl-ton::tl-get (getf world :shard-id) :root-hash)
                                                                                :file-hash (cl-ton::tl-get (getf world :shard-id) :file-hash))))
                              (and (null (cl-ton::tonnode-watch-set wl hit (list :exists t :balance 1) older wnew))
                                   (not (eql 1 (getf (cl-ton::tonnode-watch-get wl hit) :balance))))))
                     (check "watchlist: a cold read of a stale account sets it (proved against its shard block's state hash)"
                            (and (cl-ton::tonnode-watch-set wl miss (list :exists nil) (getf world :shard-id) wnew)
                                 (not (getf (cl-ton::tonnode-watch-get wl miss) :stale)) (null (cl-ton::tonnode-watch-stale wl))))
                     (check "watchlist: a resync of the shard makes its watched accounts stale again (blocks were skipped)"
                            (progn (cl-ton::tonnode-watch-blocks wl '() (list (list :id (getf world :shard-id) :skipped 1000)))
                                   (and (= 2 (length (cl-ton::tonnode-watch-stale wl)))
                                        (getf (cl-ton::tonnode-watch-get wl hit) :balance))))
                     (check "account-cell-balance: for all 12 accounts the block changed, the balance read from the Account cell equals the one of the state update (DepthBalanceInfo)"
                          (every (lambda (c)
                                   (let ((a (cl-ton::block-new-shard-account wblock (getf c :account))))
                                     (or (not (getf a :exists))
                                         (eql (getf a :balance) (cl-ton::account-cell-balance (getf a :account-cell))))))
                                 changes))
                   (check "account-cell-balance: some of those accounts really have a balance (the check above is not about zeros)"
                          (some (lambda (c) (let ((a (cl-ton::block-new-shard-account wblock (getf c :account))))
                                              (and (getf a :exists) (plusp (cl-ton::account-cell-balance (getf a :account-cell))))))
                                changes))
                   ;; --- refresh of stale accounts by cold reads
                   (let* ((wl2 (cl-ton::make-tonnode-watchlist))
                          (fol (cl-ton::make-tonnode-follower :mc-id (%tn-t-id 104057524)
                                                              :shards (list (list :id (getf world :shard-id) :state-hash wnew))))
                          (reads 0)
                          (good (lambda (account mc) (declare (ignore mc)) (incf reads)
                                  (let ((a (cl-ton::block-new-shard-account wblock account)))
                                    (list :exists t :account-cell (getf a :account-cell) :last-trans-lt (getf a :last-trans-lt)
                                          :last-trans-hash (getf a :last-trans-hash) :shard-block (getf world :shard-id) :state-hash wnew)))))
                     (cl-ton::tonnode-watch-add wl2 hit) (cl-ton::tonnode-watch-add wl2 hit2)
                     (check "refresh: two stale accounts are read again, each stored with the balance computed from its Account cell, none stale after"
                            (and (= 2 (length (cl-ton::tonnode-watch-refresh wl2 fol good))) (= 2 reads) (null (cl-ton::tonnode-watch-stale wl2))
                                 (eql (getf (cl-ton::tonnode-watch-get wl2 hit) :balance)
                                      (getf (cl-ton::block-new-shard-account wblock hit) :balance))))
                     (check "refresh: nothing stale, nothing read"
                            (progn (cl-ton::tonnode-watch-refresh wl2 fol good) (= 2 reads)))
                     (let ((wl3 (cl-ton::make-tonnode-watchlist)))
                       (cl-ton::tonnode-watch-add wl3 hit)
                       (check "refresh: a proof against a state the follower does not hold, or an error of the reader, leaves the account stale"
                              (and (null (cl-ton::tonnode-watch-refresh
                                          wl3 fol (lambda (a mc) (let ((r (funcall good a mc))) (setf (getf r :state-hash) (make-array 32 :element-type '(unsigned-byte 8) :initial-element 5)) r))))
                                   (null (cl-ton::tonnode-watch-refresh wl3 fol (lambda (a mc) (declare (ignore a mc)) (error "liteserver down"))))
                                   (equal (cl-ton::tonnode-watch-stale wl3) (list (cl-ton::octets->hex hit)))))))
                   (check "watchlist: a block that does not name a watched account is not read further; removing an account forgets it"
                            (let ((empty (cl-ton::make-tonnode-watchlist)))
                              (and (null (cl-ton::tonnode-watch-blocks empty blocks))
                                   (progn (cl-ton::tonnode-watch-remove wl hit) (null (cl-ton::tonnode-watch-get wl hit)))))))))
               ;; the follower was away: the held tip is 1000 blocks behind: no walk, a fresh start from the tip, said so
               (let* ((far-id (cl-ton::tl-make "tonNode.blockIdExt" :workchain 0 :shard (cl-ton::%signed64 #x8000000000000000) :seqno (- 108759255 1000)
                                                                    :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 3)
                                                                    :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 4)))
                      (away (cl-ton::make-tonnode-follower :shards (list (list :id far-id :state-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 5))))))
                 (multiple-value-bind (blocks resynced) (cl-ton::tonnode-follower-apply away (pool :a) descrs :max-blocks 32 :timeout 3)
                   (check "follower: a tip far ahead of the held one is not walked: a fresh start from the tip, with the number of skipped blocks"
                          (and (null blocks) (= 1 (length resynced)) (= 1000 (getf (first resynced) :skipped))
                               (= 1 (length (cl-ton::tfollower-shards away)))
                               (cl-ton::%same-block-id-p (getf (first (cl-ton::tfollower-shards away)) :id) (getf world :shard-id))
                               (= 32 (length (getf (first (cl-ton::tfollower-shards away)) :state-hash)))))))
               (let ((wrong (cl-ton::make-tonnode-follower
                             :shards (list (list :id prev-id :state-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 9))))))
                 (check "follower: a block that does not start from the state held is refused and nothing changes (PROOF-ERROR)"
                        (and (handler-case (progn (cl-ton::tonnode-follower-apply wrong (pool :a) descrs :timeout 3) nil)
                               (cl-ton::proof-error () t))
                             (cl-ton::%same-block-id-p (getf (first (cl-ton::tfollower-shards wrong)) :id) prev-id)))))
             (check "pool error: the message says how the peers failed (silent / answered wrongly / without the block)"
                    (let ((text (handler-case (progn (cl-ton::tonnode-download-block (pool :silent) (getf world :block-id) :timeout 1) nil)
                                  (cl-ton::tonnode-error (e) (princ-to-string e)))))
                      (and text (search "silent" text) (search "answered wrongly" text) (search "peers" text))))
             (check "pool: eight silent peers and one good one: the attempts widen and the good one is found (no luck needed)"
                    (equalp (cl-ton::tonnode-download-block (pool :silent :silent :silent :silent :silent :silent :silent :silent :a)
                                                            (getf world :block-id) :timeout 1)
                            (getf world :block)))
             (let ((p (pool :fresh)) (th (sb-thread:make-thread (lambda () (sleep 1.0) (setf (car gate) t)))))
               (multiple-value-bind (block info) (cl-ton::tonnode-verified-masterchain-block p (getf world :block-id) key-cell :timeout 1 :round-pause 0.3)
                 (declare (ignore block))
                 (check "masterchain block whose proof appears a moment late: the first round finds nothing, a later round gets the proof"
                        (= 103977810 (getf info :seqno))))
               (sb-thread:join-thread th)
               (setf (car gate) nil)
               (check "masterchain block nobody has a proof for: TONNODE-ERROR after the rounds"
                      (handler-case (progn (cl-ton::tonnode-verified-masterchain-block (pool :fresh) (getf world :block-id) key-cell :timeout 1 :rounds 2 :round-pause 0.1) nil)
                        (cl-ton::tonnode-error () t))))
             (let ((p (pool :silent :silent :silent :silent :silent :silent :a)))
               (cl-ton::tonnode-download-block p (getf world :block-id) :timeout 1)
               (sleep 1.2)                      ; the silent workers finish and are noted
               (check "pool ranking: the peer that answered comes first, before peers that failed and never answered (fix 94)"
                      (eq (first (cl-ton::%tn-pick p 1 nil nil)) (car (last (cl-ton::tnp-peers p)))))
               (let* ((t0 (get-internal-real-time))
                      (data (cl-ton::tonnode-download-block p (getf world :block-id) :timeout 3))
                      (secs (/ (- (get-internal-real-time) t0) internal-time-units-per-second 1.0)))
                 (check "pool ranking: the next call is answered at once by the known peer, no timeout of the silent ones is waited for"
                        (and (equalp data (getf world :block)) (< secs 1.0)))))
             (let ((p (pool :fresh :a)))
               (setf (car gate) nil)
               (ignore-errors (cl-ton::tonnode-download-block-proof p (getf world :block-id) :timeout 1 :prepare nil :attempts 1 :blame nil))
               (sleep 1.2)
               (check "silence not blamed (a block too new for a proof): no failure counted, no cool-down"
                      (every (lambda (peer) (and (zerop (cl-ton::tn-peer-streak peer)) (zerop (cl-ton::tn-peer-bad peer)))) (cl-ton::tnp-peers p))))
             ;; --- fix 96: catching up (lz4, the masterchain blocks in batches, the shard blocks in parallel into a cache)
             (let* ((s1 (%tn-t-octets (apply #'concatenate 'string (make-list 20 :initial-element "abcabcabc"))))
                    (s2 (concatenate '(simple-array (unsigned-byte 8) (*)) (coerce (loop for i below 256 collect i) '(simple-array (unsigned-byte 8) (*)))
                                     (coerce (loop for i below 256 collect i) '(simple-array (unsigned-byte 8) (*))) (%tn-t-octets (apply #'concatenate 'string (make-list 100 :initial-element "xyz")))))
                    (s2z "fff1000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f505152535455565758595a5b5c5d5e5f606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeafb0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff0001ed3f78797a0300ff1250797a78797a")
                    (s3 "82b70eee7f1a5039bef07ec2347f066ed08f5dc7512447e3404300026b6e545594a065685d64c4980bb8d4544a8721a99a01ad219eb59cf6a15ef6f15a1d830bb7ce09d6bbc004e7175c643c7decb0b580ec37bc9712dd2e6aaeb94bae8d2f9fa29c5a284c9ef7521829cf1079b080e9d74a1c10fcab6a4243d33656debe4c1ed79648e856e8f9a2f58c95f0ce4b39c15bffad5c2dfb8bb820b6119cba8ff88796ae5b05f280a68ced93b6b28cb0d1b358e6baab485565b9f49028d557d79a8a0e6451e15c705c15f173541b4438a25cf76312d4eeb3c2246879bf00b3cf8ed13abf129a3097ad96b442d6d1bdef4850c3f465442eb300c337a648a6c0dbdd73fc95f5c2c451859afe80d40aa39dfb9249f40c3ee37d961445c806f58c7cf2127dfa894f9296fcf33c084099"))
               (check "lz4: a block made by liblz4 with matches that overlap their own output and a match length with extension bytes"
                      (equalp s1 (cl-ton::lz4-decompress (cl-ton::hex->octets "3f616263030099506263616263"))))
               (check "lz4: a block of liblz4 with literal runs and match lengths longer than 15 (extension bytes) comes out right"
                      (equalp s2 (cl-ton::lz4-decompress (cl-ton::hex->octets s2z))))
               (check "lz4: the literals-only block the test compressor makes decodes (a run of 300 literals)"
                      (equalp (cl-ton::hex->octets s3) (cl-ton::lz4-decompress (%tn-t-lz4-literals (cl-ton::hex->octets s3)))))
               (check "lz4: truncated input, an offset of zero and more output than allowed are TONNODE-ERRORs, not garbage"
                      (every (lambda (thunk) (handler-case (progn (funcall thunk) nil) (cl-ton::tonnode-error () t)))
                             (list (lambda () (cl-ton::lz4-decompress (subseq (cl-ton::hex->octets s2z) 0 100)))
                                   (lambda () (cl-ton::lz4-decompress (cl-ton::hex->octets "10610000")))
                                   (lambda () (cl-ton::lz4-decompress (cl-ton::hex->octets "3f616263030099506263616263") :max-size 100))))))
             (let ((prev (%tn-t-id (1- 103977810))))
               (dolist (kind '(:nextplain :nextz))
                 (let ((got (cl-ton::tonnode-next-masterchain-blocks (pool kind) prev :timeout 4)))
                   (check (format nil "next masterchain blocks (~A): the block comes back, with the id the peer names, its cell hashing to the root hash" kind)
                          (and (= 1 (length got)) (cl-ton::%same-block-id-p (getf (first got) :id) (getf world :block-id))))))
               (check "next masterchain blocks: a peer that has no block after the one asked gives none (no error)"
                      (null (cl-ton::tonnode-next-masterchain-blocks (pool :nextz) (%tn-t-id 5) :timeout 3)))
               (check "masterchain range: the batches reach the asked seqno, and the seconds and blocks of each query are given"
                      (multiple-value-bind (blocks batches) (cl-ton::tonnode-masterchain-range (pool :nextz) prev 103977810 :timeout 4)
                        (and (= 1 (length blocks)) (= 1 (length batches)) (= 1 (second (first batches))) (eq :batch (third (first batches))) (realp (first (first batches))))))
               (check "masterchain range: peers whose batch answers are empty but that give the next block singly: the blocks come one by one (fix 99)"
                      (multiple-value-bind (blocks queries) (cl-ton::tonnode-masterchain-range (pool :nextsingle) prev 103977810 :timeout 4)
                        (and (= 1 (length blocks)) (cl-ton::%same-block-id-p (getf (first blocks) :id) (getf world :block-id))
                             (find :single queries :key #'third))))
               (check "next masterchain block (single): the block comes back with its proof cell; a peer with nothing gives none"
                      (and (getf (first (cl-ton::tonnode-next-masterchain-block (pool :nextsingle) prev :timeout 3)) :proof)
                           (null (cl-ton::tonnode-next-masterchain-block (pool :nextsingle) (%tn-t-id 5) :timeout 3))))
               (check "next masterchain blocks: peers that answer with nothing do not end the search, the widening finds the peer that has the block"
                      (= 1 (length (cl-ton::tonnode-next-masterchain-blocks (pool :nextempty :nextempty :nextempty :nextz) prev :timeout 4))))
               (let ((ids (cl-ton::%hint-shard-ids (cl-ton::tonnode-masterchain-range (pool :nextz) prev 103977810 :timeout 4) 0)))
                 (check "hints: the masterchain block names basechain shard blocks, each id once"
                        (and ids (every (lambda (id) (= 0 (cl-ton::tl-get id :workchain))) ids)
                             (= (length ids) (length (remove-duplicates (mapcar (lambda (id) (cl-ton::tl-get id :seqno)) ids))))))))
             (multiple-value-bind (block) (cl-ton::tonnode-verified-block (pool :a) (getf world :shard-id) :timeout 3)
               (let ((prev-id (cl-ton::shard-descr-block-id (first (cl-ton::parse-block-links block (getf world :shard-id))))))
                 (multiple-value-bind (cache stats) (cl-ton::tonnode-prefetch-blocks (pool :count) (list (getf world :shard-id) (%tn-t-id 7)) :timeout 2 :parallel 3)
                   (check "prefetch: the block that exists lands in the cache, the one nobody has is counted as failed, no error"
                          (and (= 1 (getf stats :fetched)) (= 1 (getf stats :failed)) (= (length (getf world :shard-block)) (getf stats :bytes))
                               (equalp (getf world :shard-block) (sixth (gethash (cl-ton::as-octets (cl-ton::tl-get (getf world :shard-id) :file-hash)) cache)))))
                   (check "prefetch: the peer was asked (downloads counted)" (plusp (car dl)))
                   (check "prefetch (fix 100): the cache holds the block already read (verified entry), and TONNODE-VERIFIED-BLOCK takes it with no peer able to answer"
                          (multiple-value-bind (b1 i1 n1 o1) (cl-ton::tonnode-verified-block (pool :a) (getf world :shard-id) :timeout 3)
                            (multiple-value-bind (b2 i2 n2 o2 oc2) (cl-ton::tonnode-verified-block (pool :silent) (getf world :shard-id) :timeout 1 :cache cache)
                              (and (eq b2 (second (gethash (cl-ton::as-octets (cl-ton::tl-get (getf world :shard-id) :file-hash)) cache)))
                                   (equalp i1 i2) (equalp n1 n2) (equalp o1 o2) (equalp oc2 (getf world :shard-block)) b1))))
                   (let ((pf (cl-ton::tonnode-start-prefetcher (pool :a) :parallel 2 :timeout 2)))
                     (cl-ton::prefetcher-add pf (list (getf world :shard-id)))
                     (cl-ton::prefetcher-add pf (list (getf world :shard-id)))      ; the same id again: not queued twice
                     (multiple-value-bind (c st) (cl-ton::prefetcher-finish pf)
                       (check "prefetcher: ids added in several calls, an id twice is fetched once, the result is in the cache"
                              (and (= 1 (getf st :ids)) (= 1 (getf st :fetched)) (= 0 (getf st :failed)) (= 1 (hash-table-count c))))))
                   (let ((chain (cl-ton::tonnode-shard-chain (pool :silent) (getf world :shard-id) prev-id :timeout 1 :cache cache)))
                     (check "shard chain with a cache: the walk takes the block from the cache, with no peer able to answer (all the same checks)"
                            (and (= 1 (length chain)) (= 108759255 (getf (getf (first chain) :info) :seqno)))))
                   (let ((poisoned (make-hash-table :test 'equalp)))
                     (setf (gethash (cl-ton::as-octets (cl-ton::tl-get (getf world :shard-id) :file-hash)) poisoned)
                           (let ((c (copy-seq (getf world :shard-block)))) (setf (aref c 100) (logxor 1 (aref c 100))) c))
                     (check "a cache with a wrong file in it passes nothing: the file is checked again, and without an answering peer the walk fails"
                            (handler-case (progn (cl-ton::tonnode-shard-chain (pool :silent) (getf world :shard-id) prev-id :timeout 1 :cache poisoned) nil)
                              (cl-ton::tonnode-error () t)))
                     (check "...and with an honest peer the real block is fetched in place of the wrong one"
                            (= 1 (length (cl-ton::tonnode-shard-chain (pool :a) (getf world :shard-id) prev-id :timeout 3 :cache poisoned)))))))) 
             ;; --- fix 97: the follower goes on by itself: blocks and proofs from the nodes, the hash chain from its own block
             (let* ((mc-block (first (cl-ton::parse-boc (getf world :block))))
                    (prev (cl-ton::shard-descr-block-id (first (cl-ton::parse-block-links mc-block (getf world :block-id)))))
                    (tips (mapcar #'cl-ton::shard-descr-block-id (remove-if-not (lambda (d) (= 0 (getf d :workchain))) (cl-ton::block-shard-descriptions mc-block))))
                    (mk (lambda (mc-id) (cl-ton::make-tonnode-follower
                                         :key-block key-cell :mc-id mc-id
                                         :shards (mapcar (lambda (tip) (list :id tip :state-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))) tips)))))
               (dolist (kind '(:nextz :nextplain))
                 (let ((f (funcall mk prev)))
                   (multiple-value-bind (new-blocks info state-hash resynced weight total) (cl-ton::tonnode-follower-advance f (pool kind) (pool :a) :timeout 4)
                     (check (format nil "advance (~A): the next masterchain block comes with its proof, is proven by the key block's validators and becomes the follower's block" kind)
                            (and (null new-blocks) (null resynced) (= 103977810 (getf info :seqno)) (= 32 (length state-hash))
                                 (cl-ton::%same-block-id-p (cl-ton::tfollower-mc-id f) (getf world :block-id)) (> (* 3 weight) (* 2 total)))))))
               (let ((f (funcall mk (getf world :block-id))))
                 (check "advance: when the nodes have no newer block with a proof there is no result and the follower stays"
                        (and (null (cl-ton::tonnode-follower-advance f (pool :nextz) (pool :a) :timeout 3))
                             (cl-ton::%same-block-id-p (cl-ton::tfollower-mc-id f) (getf world :block-id)))))
               (let ((f (funcall mk (%tn-t-id 103977809))))
                 (check "advance: a block that does not follow the follower's own (its predecessor reference names another) is a PROOF-ERROR, nothing changes"
                        (and (handler-case (progn (cl-ton::tonnode-follower-advance f (pool :nextz) (pool :a) :timeout 3) nil)
                               (cl-ton::proof-error () t))
                             (cl-ton::%same-block-id-p (cl-ton::tfollower-mc-id f) (%tn-t-id 103977809)))))
               (check "advance: a follower with no masterchain block yet is told to take a step first (TONNODE-ERROR)"
                      (handler-case (progn (cl-ton::tonnode-follower-advance (cl-ton::make-tonnode-follower :key-block key-cell) (pool :nextz) (pool :a)) nil)
                        (cl-ton::tonnode-error () t)))
               ;; --- fix 103: the run loop (retries, first step from a head id, the watchlist after every step)
               (let* ((f (funcall mk prev)) (calls '()) (wl (cl-ton::make-tonnode-watchlist))
                      (n (cl-ton::tonnode-follower-run f (pool :nextz) (pool :a) :steps 1 :timeout 4 :pause 0 :watchlist wl
                                                                                  :on-step (lambda (r) (push r calls)))))
                 (check "run: one step is made, ON-STEP gets the result with the new block, the follower has moved and the empty watchlist gave no events"
                        (and (= 1 n) (= 1 (length calls)) (= 103977810 (getf (getf (first calls) :info) :seqno))
                             (null (getf (first calls) :events)) (numberp (getf (first calls) :seconds))
                             (cl-ton::%same-block-id-p (cl-ton::tfollower-mc-id f) (getf world :block-id)))))
               (let* ((f (funcall mk (%tn-t-id 103977809))) (seen '()))
                 (check "run: a step that fails again and again is retried (ON-ERROR told each time) and the error is signalled after MAX-FAILURES; the follower is unchanged"
                        (and (handler-case (progn (cl-ton::tonnode-follower-run f (pool :nextz) (pool :a) :timeout 3 :pause 0 :max-failures 2
                                                                                                          :on-error (lambda (e k) (declare (ignore e)) (push k seen)))
                                                  nil)
                               (cl-ton::proof-error () t))
                             (equal (reverse seen) '(1 2))
                             (cl-ton::%same-block-id-p (cl-ton::tfollower-mc-id f) (%tn-t-id 103977809)))))
               (let ((f (cl-ton::make-tonnode-follower :key-block key-cell)))
                 (check "run: a follower with no masterchain block and no HEAD-FN cannot start (TONNODE-ERROR after MAX-FAILURES)"
                        (handler-case (progn (cl-ton::tonnode-follower-run f (pool :nextz) (pool :a) :pause 0 :max-failures 2) nil)
                          (cl-ton::tonnode-error () t))))
               (let ((f (cl-ton::make-tonnode-follower :key-block key-cell)) (heads 0) (seen '()))
                 (check "run: the first step is taken from the block id HEAD-FN gives (here the basechain tip is not served: the failure is told, then signalled)"
                        (and (handler-case (progn (cl-ton::tonnode-follower-run f (pool :a) (pool :a) :timeout 2 :pause 0 :max-failures 1
                                                                                                    :head-fn (lambda () (incf heads) (getf world :block-id))
                                                                                                    :on-error (lambda (e k) (declare (ignore k)) (push e seen)))
                                                  nil)
                               (cl-ton::tonnode-error () t))
                             (= 1 heads) (= 1 (length seen)))))
               ;; --- fix 104: the head decides between going on and a fresh step
               (let* ((f (funcall mk prev)) (heads 0) (fresh-seen '())
                      (n (cl-ton::tonnode-follower-run f (pool :nextz) (pool :a) :steps 1 :timeout 4 :pause 0
                                                                                 :head-fn (lambda () (incf heads) (getf world :block-id))
                                                                                 :on-step (lambda (r) (push (getf r :fresh) fresh-seen)))))
                 (check "run: with HEAD-FN, a follower one block behind the head goes on by advance (the head was asked on the first step, no fresh step)"
                        (and (= 1 n) (= 1 heads) (equal fresh-seen '(nil)) (cl-ton::%same-block-id-p (cl-ton::tfollower-mc-id f) (getf world :block-id)))))
               (let* ((f (funcall mk prev)) (heads 0) (seen '()))
                 (check "run: a follower 1000 blocks behind the head takes a FRESH step from the head id (here the nodes do not serve it: failure told, then signalled), the follower is unchanged"
                        (and (handler-case (progn (cl-ton::tonnode-follower-run f (pool :nextz) (pool :a) :timeout 2 :pause 0 :max-failures 1
                                                                                                  :head-fn (lambda () (incf heads) (%tn-t-id (+ 103977809 1000)))
                                                                                                  :on-error (lambda (e k) (declare (ignore k)) (push e seen)))
                                                  nil)
                               (cl-ton::tonnode-error () t))
                             (= 1 heads) (= 1 (length seen))
                             (cl-ton::%same-block-id-p (cl-ton::tfollower-mc-id f) prev))))
               (let* ((f (funcall mk prev)) (heads 0) (seen '()))
                 (check "run: a HEAD-FN that fails (any error) is a failed step like the others: told, retried, then signalled as TONNODE-ERROR"
                        (and (handler-case (progn (cl-ton::tonnode-follower-run f (pool :nextz) (pool :a) :timeout 2 :pause 0 :max-failures 2
                                                                                                  :head-fn (lambda () (incf heads) (error "the liteserver is down"))
                                                                                                  :on-error (lambda (e k) (declare (ignore k)) (push e seen)))
                                                  nil)
                               (cl-ton::tonnode-error () t))
                             (= 2 heads) (= 2 (length seen)))))
               (let ((f (funcall mk (getf world :block-id))) (polls 0))
                 (check "run: when the nodes have nothing newer the loop waits and goes on until STOP says so; no step is counted"
                        (and (eql 0 (cl-ton::tonnode-follower-run f (pool :nextz) (pool :a) :timeout 3 :pause 0 :stop (lambda () (> (incf polls) 2))))
                             (= 3 polls)))))
             ;; --- fix 101: the overlay broadcast (Gate 5: accepted by a real node 2026.10 from a non-member: see the ledger)
             (let* ((kp (cl-ton::adnl-generate-keypair))
                    (ov (coerce (loop for i below 32 collect (* 7 i)) '(simple-array (unsigned-byte 8) (*))))
                    (data (%tn-t-octets "an external message boc stand-in"))
                    (octets (cl-ton::overlay-broadcast-octets ov kp data :date 1700000000 :flags 0)))
               (multiple-value-bind (msg rest) (cl-ton::tl-decode-prefix octets)
                 (let ((bc (cl-ton::tl-decode rest)))
                   (check "broadcast: the payload starts with the boxed overlay.message of the overlay"
                          (and (cl-ton::tl-is msg "overlay.message") (equalp (cl-ton::tl-get msg :overlay) ov)))
                   (check "broadcast: an overlay.broadcast with the sender's key, no certificate, the flags, the data and the date"
                          (and (cl-ton::tl-is bc "overlay.broadcast") (equalp (cl-ton::tl-get (cl-ton::tl-get bc :src) :key) (cl-ton::keypair-public kp))
                               (cl-ton::tl-is (cl-ton::tl-get bc :certificate) "overlay.emptyCertificate")
                               (= 0 (cl-ton::tl-get bc :flags)) (equalp (cl-ton::tl-get bc :data) data) (= 1700000000 (cl-ton::tl-get bc :date))))
                   (let* ((hash (cl-ton::sha256 (cl-ton::tl-encode (cl-ton::tl-make "overlay.broadcast.id"
                                                                                    :src (coerce (cl-ton::adnl-short-id (cl-ton::keypair-public kp)) 'cl-ton::tl-octets)
                                                                                    :data-hash (coerce (cl-ton::sha256 data) 'cl-ton::tl-octets) :flags 0))))
                          (to-sign (cl-ton::tl-encode (cl-ton::tl-make "overlay.broadcast.toSign" :hash (coerce hash 'cl-ton::tl-octets) :date 1700000000))))
                     (check "broadcast: the signature verifies over overlay.broadcast.toSign{sha256 of overlay.broadcast.id, date} with the sender's key"
                            (ironclad:verify-signature (ironclad:make-public-key :ed25519 :y (cl-ton::keypair-public kp)) to-sign
                                                       (cl-ton::as-octets (cl-ton::tl-get bc :signature))))))))
             (check "external message broadcast: a tonNode.externalMessageBroadcast carrying the message octets"
                    (let ((o (cl-ton::tl-decode (cl-ton::external-message-broadcast-octets (%tn-t-octets "abc")))))
                      (and (cl-ton::tl-is o "tonNode.externalMessageBroadcast")
                           (equalp (cl-ton::tl-get (cl-ton::tl-get o :message) :data) (%tn-t-octets "abc")))))
             (let* ((got nil)
                    (b (cl-ton::adnl-udp-start :host "127.0.0.1" :port 0 :custom-handler (lambda (octets sender) (declare (ignore sender)) (setf got octets))))
                    (a (cl-ton::adnl-udp-start :host "127.0.0.1" :port 0))
                    (ov (coerce (loop for i below 32 collect i) '(simple-array (unsigned-byte 8) (*)))))
               (unwind-protect
                    (progn
                      (cl-ton::overlay-send-broadcast a "127.0.0.1" (cl-ton::adnl-udp-port b) (cl-ton::keypair-public (cl-ton::adnl-udp-keypair b)) ov
                                                      (cl-ton::adnl-udp-keypair a) (%tn-t-octets "payload"))
                      (loop repeat 30 until got do (sleep 0.1))
                      (check "broadcast over ADNL UDP: the receiving node gets the custom message, an overlay.message + overlay.broadcast with the data"
                             (and got (multiple-value-bind (msg rest) (cl-ton::tl-decode-prefix got)
                                        (and (cl-ton::tl-is msg "overlay.message")
                                             (equalp (cl-ton::tl-get (cl-ton::tl-decode rest) :data) (%tn-t-octets "payload")))))))
                 (cl-ton::adnl-udp-stop a) (cl-ton::adnl-udp-stop b)))
             (let* ((got-a nil) (got-b nil)
                    (b1 (cl-ton::adnl-udp-start :host "127.0.0.1" :port 0 :custom-handler (lambda (o s) (declare (ignore s)) (setf got-a o))))
                    (b2 (cl-ton::adnl-udp-start :host "127.0.0.1" :port 0 :custom-handler (lambda (o s) (declare (ignore s)) (setf got-b o))))
                    (cnode (cl-ton::adnl-udp-start :host "127.0.0.1" :port 0))
                    (ov (coerce (loop for i below 32 collect (+ 100 i)) '(simple-array (unsigned-byte 8) (*))))
                    (pf (cl-ton::make-tonnode-pool (cl-ton::make-overlay-client cnode) ov
                                                   (list (list "127.0.0.1" (cl-ton::adnl-udp-port b1) (cl-ton::keypair-public (cl-ton::adnl-udp-keypair b1)))
                                                         (list "127.0.0.1" (cl-ton::adnl-udp-port b2) (cl-ton::keypair-public (cl-ton::adnl-udp-keypair b2)))))))
               (unwind-protect
                    (let ((sent (cl-ton::tonnode-send-external-message pf (%tn-t-octets "boc-of-an-external-message") :count 2 :repeat 1)))
                      (loop repeat 30 until (and got-a got-b) do (sleep 0.1))
                      (check "send external message: broadcast to the asked number of pool members, each gets an overlay.message + broadcast carrying the externalMessageBroadcast"
                             (and (= 2 (length sent)) got-a got-b
                                  (every (lambda (got)
                                           (multiple-value-bind (msg rest) (cl-ton::tl-decode-prefix got)
                                             (let* ((bc (cl-ton::tl-decode rest))
                                                    (inner (cl-ton::tl-decode (cl-ton::tl-get bc :data))))
                                               (and (cl-ton::tl-is msg "overlay.message") (equalp (cl-ton::tl-get msg :overlay) ov)
                                                    (cl-ton::tl-is inner "tonNode.externalMessageBroadcast")
                                                    (equalp (cl-ton::tl-get (cl-ton::tl-get inner :message) :data) (%tn-t-octets "boc-of-an-external-message"))))))
                                         (list got-a got-b)))))
                 (cl-ton::adnl-udp-stop b1) (cl-ton::adnl-udp-stop b2) (cl-ton::adnl-udp-stop cnode)))
             (check "block without prepareBlock: asked for at once, a liar and a silent peer skipped, the good one's file checked"
                    (equalp (cl-ton::tonnode-download-block (pool :silent :liar :a) (getf world :block-id) :timeout 2 :prepare nil)
                            (getf world :block)))
             (check "block without prepareBlock: a peer that answers without the file is 'without the block' and not held against it"
                    (let ((p (pool :a)))
                      (and (handler-case (progn (cl-ton::tonnode-download-block p (cl-ton::shard-descr-block-id
                                                                                  (list :workchain 0 :shard #x8000000000000000 :seqno 1
                                                                                        :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 1)
                                                                                        :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 2)))
                                                                    :timeout 2 :prepare nil)
                                                nil)
                             (cl-ton::tonnode-error (e) (and (search "without the block" (princ-to-string e)) (not (search "answered wrongly, 0" (princ-to-string e))) t)))
                           ;; the same peer still serves a block it has
                           (equalp (cl-ton::tonnode-download-block p (getf world :block-id) :timeout 2 :prepare nil) (getf world :block)))))
             (check "verified block: a peer that serves a damaged file gives no block (TONNODE-ERROR)"
                    (handler-case (progn (cl-ton::tonnode-verified-block (pool :liar) (getf world :block-id) :timeout 3) nil)
                      (cl-ton::tonnode-error () t))))
        (dolist (n nodes) (%oq-t-stop-node (cdr n)))
        (cl-ton::adnl-udp-stop (cl-ton::ocl-node client))))))
