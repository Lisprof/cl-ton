;;;; tests/tl-adnl-ext.lisp -- network-free unit tests for Phase A (TL codec)
;;;; and Phase B (ADNL-ext crypto/framing).
;;;;
;;;; Pinned constructor ids were located INSIDE the released tonlib binary
;;;; (little-endian bytes searched in lib/tonlibjson-linux-x86_64.so), not
;;;; taken from memory; the presence check below re-verifies that whenever the
;;;; .so is on disk.  The four ids known NOT to occur in it (results tonlib
;;;; never appears to decode) are deliberately not pinned.
(in-package :cl-ton/test)

(defun %o (&rest bytes) (coerce bytes '(simple-array (unsigned-byte 8) (*))))
(defun %hex (s) (cl-ton::hex->octets s))

(defun %slurp (path)
  (with-open-file (s path :element-type '(unsigned-byte 8))
    (let ((v (make-array (file-length s) :element-type '(unsigned-byte 8))))
      (read-sequence v s) v)))

(defun %tonlib-so ()
  (let ((p (%lib "tonlibjson-linux-x86_64.so")))
    (when p (%slurp p))))

(defun %id-le (id)
  (coerce (loop for i below 4 collect (ldb (byte 8 (* 8 i)) id)) '(simple-array (unsigned-byte 8) (*))))

(defmacro %signals (condition &body body)
  `(handler-case (progn ,@body nil) (,condition () t)))

(defparameter *pinned-ids*
  '(("tcp.ping" #x4D082B9A) ("tcp.pong" #xDC69FB03)
    ("adnl.message.query" #xB48BF97A) ("adnl.message.answer" #x0FAC8416)
    ("pub.ed25519" #x4813B4C6) ("pk.ed25519" #x49682317)
    ("liteServer.query" #x798C06DF) ("liteServer.getMasterchainInfo" #x89B5E62E)
    ("liteServer.waitMasterchainSeqno" #xBAEAB892)
    ;; vector-bearing ids: wrong unless the tl-parser paren normalisation is applied
    ("liteServer.getConfigParams" #x2A111C19) ("liteServer.transactionList" #x6F26C60B)))

(defparameter *absent-from-tonlib-binary*
  '("liteServer.currentTime" "liteServer.blockData" "liteServer.blockState" "liteServer.shardInfo"
    "liteServer.transactionInfo" "liteServer.validatorStats" "liteServer.accountDispatchQueueInfo"
    "liteServer.dispatchQueueInfo" "liteServer.dispatchQueueMessage" "liteServer.dispatchQueueMessages"
    "liteServer.debug.verbosity" "liteServer.nonfinal.candidateId" "liteServer.nonfinal.candidate"
    "liteServer.nonfinal.candidateInfo" "liteServer.nonfinal.validatorGroupInfo"
    "liteServer.nonfinal.validatorGroups" "liteServer.nonfinal.pendingShardBlocks")
  "The schema constructors whose ids do not occur in libtonlibjson: tonlib forwards or never
parses these (results it does not look into, queries it does not send, validator-engine
control objects).  Every other constructor's id must occur there.")

(defun %ids-in-so (so)
  "The set (hash table) of 32-bit little-endian words of SO, restricted to registered constructor
ids -- one pass over the library."
  (declare (type (simple-array (unsigned-byte 8) (*)) so) (optimize speed))
  (let ((found (make-hash-table)))
    (loop for i of-type fixnum from 0 below (- (length so) 3)
          for w of-type (unsigned-byte 32) = (logior (aref so i) (ash (aref so (+ i 1)) 8)
                                                     (ash (aref so (+ i 2)) 16) (ash (aref so (+ i 3)) 24))
          when (gethash w cl-ton::*tl-by-id*) do (setf (gethash w found) t))
    found))

(defun test-tl-ids ()
  (format t "tl constructor ids (pinned against the tonlib binary)~%")
  (check "crc32 of 123456789 = CBF43926"
         (= (cl-ton::tl-crc32-id "123456789") #xCBF43926))
  (dolist (p *pinned-ids*)
    (check (format nil "~A = ~8,'0X" (first p) (second p))
           (= (cl-ton::tl-id-of (first p)) (second p))))
  (let ((so (%tonlib-so)))
    (if so
        (let* ((found (%ids-in-so so))
               (absent (sort (loop for name being the hash-keys of cl-ton::*tl-by-name* using (hash-value con)
                                   unless (gethash (cl-ton::tl-con-id con) found) collect name)
                             #'string<)))
          (check (format nil "~D of the ~D schema ids occur in tonlibjson.so; the absent ones are exactly the ~D tonlib never parses (differences: ~S)"
                         (- (hash-table-count cl-ton::*tl-by-name*) (length absent))
                         (hash-table-count cl-ton::*tl-by-name*) (length *absent-from-tonlib-binary*)
                         (set-exclusive-or absent *absent-from-tonlib-binary* :test #'string=))
                 (null (set-exclusive-or absent *absent-from-tonlib-binary* :test #'string=))))
        (format t "  skip tonlib .so not present~%"))))

(defun test-tl-codec ()
  (format t "tl codec~%")
  (let* ((qid (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7))
         (q (cl-ton::tl-make "adnl.message.query" :query-id qid :query (%o 1 2 3)))
         (enc (cl-ton::tl-encode q))
         (dec (cl-ton::tl-decode enc)))
    (check "query wire layout: id LE, 32B query_id, len-prefixed bytes padded to 4"
           (equalp enc (concatenate '(simple-array (unsigned-byte 8) (*))
                                    (%o #x7A #xF9 #x8B #xB4) qid (%o 3 1 2 3))))
    (check "round trip keeps query_id" (equalp (cl-ton::tl-get dec :query-id) qid))
    (check "round trip keeps bytes" (equalp (cl-ton::tl-get dec :query) (%o 1 2 3))))
  (let* ((big (make-array 300 :element-type '(unsigned-byte 8) :initial-element 9))
         (e (cl-ton::tl-encode (cl-ton::tl-make "liteServer.query" :data big))))
    (check "long bytes use the 0xFE 3-byte length form" (= (aref e 4) 254))
    (check "long bytes total length padded to 4" (zerop (mod (length e) 4)))
    (check "long bytes round trip"
           (equalp (cl-ton::tl-get (cl-ton::tl-decode e) :data) big)))
  (let* ((o (cl-ton::tl-make "liteServer.error" :code -400 :message "boom"))
         (d (cl-ton::tl-decode (cl-ton::tl-encode o))))
    (check "negative int32 + string round trip"
           (and (= (cl-ton::tl-get d :code) -400) (equalp (cl-ton::tl-get d :message) "boom"))))
  (let ((d (cl-ton::tl-decode (cl-ton::tl-encode
                               (cl-ton::tl-make "liteServer.getConfigParams"
                                                :mode 0
                                                :id (cl-ton::tl-block-id-ext)
                                                :param-list '(34 0 12))))))
    (check "vector<int> round trip" (equal (coerce (cl-ton::tl-get d :param-list) 'list) '(34 0 12))))
  (let ((unk (cl-ton::tl-decode (%o #xEF #xBE #xAD #xDE 5 6 7))))
    (check "unknown constructor decodes to (id . raw)"
           (and (consp unk) (= (car unk) #xDEADBEEF) (equalp (cdr unk) (%o 5 6 7)))))
  (check "trailing octets after a known constructor are rejected"
         (%signals error (cl-ton::tl-decode
                          (concatenate '(simple-array (unsigned-byte 8) (*))
                                       (cl-ton::tl-encode (cl-ton::tl-make "tcp.ping" :random-id 1))
                                       (%o 0))))))

(defun test-adnl-ext-crypto ()
  (format t "adnl-ext crypto / framing~%")
  ;; RFC 7748 section 5.2
  (check "X25519 RFC 7748 vector 1"
         (equalp (cl-ton::x25519 (%hex "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4")
                                 (%hex "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"))
                 (%hex "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")))
  (check "X25519 RFC 7748 vector 2"
         (equalp (cl-ton::x25519 (%hex "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d")
                                 (%hex "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493"))
                 (%hex "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957")))
  (let ((nine (let ((v (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))) (setf (aref v 0) 9) v)))
    (check "X25519 RFC 7748 iterated x1"
           (equalp (cl-ton::x25519 nine nine)
                   (%hex "422c8e7a6227d7bca1350b3e2bb7279f7897b87bb6854b783c60e80311ae3079"))))
  ;; continuous CTR
  (let* ((key (make-array 32 :element-type '(unsigned-byte 8) :initial-element 1))
         (iv (make-array 16 :element-type '(unsigned-byte 8) :initial-element 2))
         (a (make-array 40 :element-type '(unsigned-byte 8) :initial-element 3))
         (b (make-array 41 :element-type '(unsigned-byte 8) :initial-element 4))
         (c1 (cl-ton::adnl-make-cipher key iv))
         (stream (concatenate '(simple-array (unsigned-byte 8) (*))
                              (cl-ton::adnl-cipher-apply c1 a) (cl-ton::adnl-cipher-apply c1 b)))
         (whole (cl-ton::adnl-cipher-apply (cl-ton::adnl-make-cipher key iv)
                                           (concatenate '(simple-array (unsigned-byte 8) (*)) a b)))
         (rekeyed (concatenate '(simple-array (unsigned-byte 8) (*))
                               (cl-ton::adnl-cipher-apply (cl-ton::adnl-make-cipher key iv) a)
                               (cl-ton::adnl-cipher-apply (cl-ton::adnl-make-cipher key iv) b))))
    (check "two calls on one cipher == one call over the concatenation" (equalp stream whole))
    (check "re-keying per packet gives a different stream" (not (equalp stream rekeyed))))
  ;; frame round trip on two paired streams, two frames in a row
  (let* ((key (make-array 32 :element-type '(unsigned-byte 8) :initial-element 5))
         (iv (make-array 16 :element-type '(unsigned-byte 8) :initial-element 6))
         (tx (cl-ton::adnl-make-cipher key iv)) (rx (cl-ton::adnl-make-cipher key iv))
         (p1 (%o 1 2 3 4))
         (p2 (make-array 1000 :element-type '(unsigned-byte 8) :initial-element 8))
         (f1 (cl-ton::adnl-encode-frame tx p1))
         (f2 (cl-ton::adnl-encode-frame tx p2)))
    (flet ((recv (frame)
             (let* ((len (cl-ton::%le-octets->integer
                          (cl-ton::adnl-cipher-apply rx (subseq frame 0 4))))
                    (plain (cl-ton::adnl-cipher-apply rx (subseq frame 4))))
               (cl-ton::adnl-check-frame-length len)
               (values (cl-ton::adnl-verify-frame plain) len))))
      (check "frame sizes = 4 + 32 + payload + 32" (and (= (length f1) 72) (= (length f2) 1068)))
      (multiple-value-bind (got len) (recv f1)
        (check "frame 1 round trip" (equalp got p1))
        (check "length field = 32 + payload + 32" (= len 68)))
      (check "frame 2 round trip on the same continuing streams" (equalp (recv f2) p2))))
  (let* ((key (make-array 32 :element-type '(unsigned-byte 8) :initial-element 5))
         (iv (make-array 16 :element-type '(unsigned-byte 8) :initial-element 6))
         (plain (cl-ton::adnl-frame-plaintext (%o 9 9 9))))
    (check "intact frame verifies" (equalp (cl-ton::adnl-verify-frame plain) (%o 9 9 9)))
    (let ((bad (copy-seq plain))) (setf (aref bad 33) (logxor 1 (aref bad 33)))
      (check "flipped payload bit rejected (bad hash)"
             (%signals cl-ton::adnl-protocol-error (cl-ton::adnl-verify-frame bad))))
    (let ((bad (copy-seq plain))) (setf (aref bad (1- (length bad))) (logxor 1 (aref bad (1- (length bad)))))
      (check "flipped hash bit rejected"
             (%signals cl-ton::adnl-protocol-error (cl-ton::adnl-verify-frame bad))))
    (check "length 63 rejected" (%signals cl-ton::adnl-protocol-error (cl-ton::adnl-check-frame-length 63)))
    (check "length 64 accepted" (null (cl-ton::adnl-check-frame-length 64)))
    (check "length 2^24 accepted" (null (cl-ton::adnl-check-frame-length (expt 2 24))))
    (check "length 2^24+1 rejected (oversize)"
           (%signals cl-ton::adnl-protocol-error (cl-ton::adnl-check-frame-length (1+ (expt 2 24)))))))

(defun test-adnl-ext-handshake ()
  (format t "adnl-ext init packet~%")
  (let* ((server (cl-ton::adnl-generate-keypair)))
    (multiple-value-bind (packet ctx crx) (cl-ton::build-init-packet (keypair-public server))
      (check "init packet is 256 octets" (= (length packet) 256))
      (check "init packet starts with the server short id"
             (equalp (subseq packet 0 32) (cl-ton::adnl-short-id (keypair-public server))))
      (multiple-value-bind (stx srx cpub) (cl-ton::decrypt-init-packet packet server)
        (check "client public key recovered" (equalp cpub (subseq packet 32 64)))
        (let ((c2s (cl-ton::adnl-cipher-apply ctx (%o 1 2 3 4 5 6 7 8)))
              (s2c (cl-ton::adnl-cipher-apply stx (%o 8 7 6 5 4 3 2 1))))
          (check "client->server stream decrypts on the server rx cipher"
                 (equalp (cl-ton::adnl-cipher-apply srx c2s) (%o 1 2 3 4 5 6 7 8)))
          (check "server->client stream decrypts on the client rx cipher"
                 (equalp (cl-ton::adnl-cipher-apply crx s2c) (%o 8 7 6 5 4 3 2 1)))))
      (check "packet for another server id is rejected"
             (%signals cl-ton::adnl-protocol-error
               (cl-ton::decrypt-init-packet packet (cl-ton::adnl-generate-keypair))))
      (let ((bad (copy-seq packet))) (setf (aref bad 200) (logxor 1 (aref bad 200)))
        (check "tampered nonce ciphertext fails the checksum"
               (%signals cl-ton::adnl-protocol-error (cl-ton::decrypt-init-packet bad server))))
      (check "short packet rejected"
             (%signals cl-ton::adnl-protocol-error (cl-ton::decrypt-init-packet (subseq packet 0 255) server)))))
  ;; direction split pinned to the released binary (first pair = SERVER->CLIENT)
  (let* ((nonce (coerce (loop for i below 160 collect i) '(simple-array (unsigned-byte 8) (*)))))
    (multiple-value-bind (tx rx) (cl-ton::adnl-session-ciphers nonce t)
      (let ((s2c (cl-ton::adnl-make-cipher (subseq nonce 0 32) (subseq nonce 64 80)))
            (c2s (cl-ton::adnl-make-cipher (subseq nonce 32 64) (subseq nonce 80 96)))
            (probe (make-array 16 :element-type '(unsigned-byte 8) :initial-element 0)))
        (check "initiator rx = first (key,iv) pair (server->client)"
               (equalp (cl-ton::adnl-cipher-apply rx probe) (cl-ton::adnl-cipher-apply s2c probe)))
        (check "initiator tx = second (key,iv) pair (client->server)"
               (equalp (cl-ton::adnl-cipher-apply tx probe) (cl-ton::adnl-cipher-apply c2s probe)))))))

(defun test-tl-adnl-ext ()
  (test-tl-ids)
  (test-tl-codec)
  (test-adnl-ext-crypto)
  (test-adnl-ext-handshake))
