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

;;;; adnl-ext.lisp -- Phase B: the ADNL-over-TCP ("ADNL-ext") transport.
;;;;
;;;; Everything both ends of a liteserver connection share:
;;;;
;;;;   * X25519 / Ed25519 glue.  ironclad has both curves but no Ed25519 ->
;;;;     Curve25519 conversion, which the handshake needs, so this file adds
;;;;     exactly that (a bignum Montgomery ladder, RFC 7748) and nothing else.
;;;;   * AES-256-CTR continuous streams: ONE cipher state per direction per
;;;;     connection.  The 4-byte length and the payload are encrypted on the
;;;;     SAME stream -- the cipher is never re-keyed per packet.
;;;;   * The frame:  enc( len32-le ) || enc( rnd32 || payload || sha256(rnd32 || payload) )
;;;;     with 64 <= len <= 2^24; the hash is verified before anything is
;;;;     dispatched and the random prefix is stripped.
;;;;   * The 256-octet init packet:
;;;;         dst-short-id (32) || sender ed25519 pubkey (32) || sha256(nonce) (32)
;;;;         || AES-CTR( nonce (160), key = secret[0..16] ++ hash[16..32],
;;;;                                  iv  = hash[0..4]    ++ secret[20..32] )
;;;;     where secret is the X25519 shared secret of (sender key, receiver
;;;;     key) and nonce carries the two (key, iv) pairs of the session:
;;;;         nonce[0..32]/[64..80]   client->server stream
;;;;         nonce[32..64]/[80..96]  server->client stream
;;;;   * Socket plumbing (read exactly N with a deadline, send all).
;;;;
;;;; Nothing here knows about liteServer queries; see adnl-ext-client.lisp
;;;; (outbound) and adnl-ext-server.lisp (inbound).

(in-package :cl-ton)

(defun %cat (&rest sequences)
  "Variadic CONCAT-OCTETS (which takes one list)."
  (concat-octets sequences))

;;; --- Curve25519 glue ---------------------------------------------------------

(defconstant +p25519+ (- (expt 2 255) 19))
(defconstant +a24-25519+ 121665)

(defun %mod-inv-25519 (x)
  (let ((result 1) (base (mod x +p25519+)) (e (- +p25519+ 2)))
    (loop while (plusp e)
          do (when (oddp e) (setf result (mod (* result base) +p25519+)))
             (setf base (mod (* base base) +p25519+)
                   e (ash e -1)))
    result))

(defun %le-octets->integer (octets)
  (let ((v 0)) (loop for i from (1- (length octets)) downto 0
                     do (setf v (logior (ash v 8) (aref octets i))))
    v))

(defun %integer->le-octets (v n)
  (let ((out (make-array n :element-type '(unsigned-byte 8))))
    (dotimes (i n) (setf (aref out i) (ldb (byte 8 (* 8 i)) v)))
    out))

(defun x25519 (scalar u-coordinate)
  "RFC 7748 X25519: SCALAR and U-COORDINATE are 32 little-endian octets."
  (let* ((k (let ((c (copy-seq scalar)))
              (setf (aref c 0) (logand (aref c 0) 248)
                    (aref c 31) (logior (logand (aref c 31) 127) 64))
              (%le-octets->integer c)))
         (u (mod (logand (%le-octets->integer u-coordinate) (1- (expt 2 255))) +p25519+))
         (x1 u) (x2 1) (z2 0) (x3 u) (z3 1) (swap 0))
    (loop for pos from 254 downto 0
          do (let ((bit (ldb (byte 1 pos) k)))
               (when (/= swap bit) (rotatef x2 x3) (rotatef z2 z3))
               (setf swap bit)
               (let* ((a (mod (+ x2 z2) +p25519+))
                      (aa (mod (* a a) +p25519+))
                      (b (mod (- x2 z2) +p25519+))
                      (bb (mod (* b b) +p25519+))
                      (e (mod (- aa bb) +p25519+))
                      (c (mod (+ x3 z3) +p25519+))
                      (d (mod (- x3 z3) +p25519+))
                      (da (mod (* d a) +p25519+))
                      (cb (mod (* c b) +p25519+)))
                 (setf x3 (mod (expt (mod (+ da cb) +p25519+) 2) +p25519+)
                       z3 (mod (* x1 (mod (expt (mod (- da cb) +p25519+) 2) +p25519+)) +p25519+)
                       x2 (mod (* aa bb) +p25519+)
                       z2 (mod (* e (mod (+ aa (mod (* +a24-25519+ e) +p25519+)) +p25519+)) +p25519+)))))
    (when (/= swap 0) (rotatef x2 x3) (rotatef z2 z3))
    (%integer->le-octets (mod (* x2 (%mod-inv-25519 z2)) +p25519+) 32)))

(defun ed25519-public->x25519 (public)
  "Montgomery u = (1+y)/(1-y) of the Edwards point with y = PUBLIC (sign bit dropped)."
  (let* ((y (logand (%le-octets->integer public) (1- (expt 2 255))))
         (u (mod (* (1+ y) (%mod-inv-25519 (mod (- 1 y) +p25519+))) +p25519+)))
    (%integer->le-octets u 32)))

(defun ed25519-seed->x25519-scalar (seed)
  "sha512(SEED)[0..32], the Ed25519 secret scalar (clamping happens in X25519)."
  (subseq (ironclad:digest-sequence :sha512 seed) 0 32))

(defun adnl-shared-secret (my-seed their-ed25519-public)
  (x25519 (ed25519-seed->x25519-scalar my-seed)
          (ed25519-public->x25519 their-ed25519-public)))

;;; --- keys / ids ------------------------------------------------------------

(defun adnl-generate-keypair ()
  "A fresh Ed25519 keypair (reusing WALLET.LISP's SEED->KEYPAIR wrapper)."
  (seed->keypair (ironclad:random-data 32)))

(defun adnl-short-id (public-key)
  "sha256 of the serialized (boxed) pub.ed25519 -- the 32-octet id a peer is
addressed by in the init packet."
  (sha256 (tl-encode (tl-make "pub.ed25519" :key (coerce public-key 'tl-octets)))))

;;; --- AES-256-CTR streams ---------------------------------------------------

(defun adnl-make-cipher (key iv)
  (ironclad:make-cipher :aes :key key :mode :ctr :initialization-vector iv))

(defun adnl-cipher-apply (cipher octets)
  "Encrypt/decrypt OCTETS (CTR is symmetric) on CIPHER's continuing stream;
returns a fresh vector."
  (let ((out (copy-seq octets)))
    (ironclad:encrypt-in-place cipher out)
    out))

;;; --- frames ----------------------------------------------------------------

(defconstant +adnl-min-packet+ 64)
(defconstant +adnl-max-packet+ (expt 2 24))

(defun adnl-frame-plaintext (payload &optional (nonce (ironclad:random-data 32)))
  "rnd32 || payload || sha256(rnd32 || payload)"
  (let* ((body (%cat nonce payload)))
    (%cat body (sha256 body))))

(defun adnl-encode-frame (cipher payload &optional (nonce (ironclad:random-data 32)))
  "The full wire frame for PAYLOAD.  Length and body are encrypted with ONE
call sequence on CIPHER, i.e. one continuous stream."
  (let* ((plain (adnl-frame-plaintext payload nonce))
         (len (length plain))
         (buf (%cat (%integer->le-octets len 4) plain)))
    (ironclad:encrypt-in-place cipher buf)
    buf))

(define-condition adnl-protocol-error (ton-error) ())
(define-condition adnl-closed (ton-error) ())

(defun adnl-protocol-error (control &rest args)
  (error 'adnl-protocol-error :format-control control :format-arguments args))

(defun adnl-check-frame-length (len)
  (unless (<= +adnl-min-packet+ len +adnl-max-packet+)
    (adnl-protocol-error "ADNL frame length ~D outside [~D, ~D]" len +adnl-min-packet+ +adnl-max-packet+)))

(defun adnl-verify-frame (plain)
  "PLAIN = rnd32 || payload || hash32 -> payload; signals ADNL-PROTOCOL-ERROR
on a bad hash.  The hash is checked BEFORE anything is dispatched."
  (let* ((n (length plain))
         (body (subseq plain 0 (- n 32)))
         (hash (subseq plain (- n 32))))
    (unless (equalp (sha256 body) hash)
      (adnl-protocol-error "ADNL frame sha256 mismatch"))
    (subseq body 32)))

;;; --- init packet -----------------------------------------------------------

(defun adnl-handshake-aes (secret checksum)
  "(VALUES key32 iv16) protecting the nonce inside the init packet."
  (values (%cat (subseq secret 0 16) (subseq checksum 16 32))
          (%cat (subseq checksum 0 4) (subseq secret 20 32))))

(defun adnl-session-ciphers (nonce initiator-p)
  "(VALUES tx-cipher rx-cipher) from the 160-octet NONCE.  Verified against
the released proxy-liteserver binary: the first (key, iv) pair
(nonce[0..32], nonce[64..80]) carries the SERVER->CLIENT stream and the second
(nonce[32..64], nonce[80..96]) the CLIENT->SERVER stream.  (The C++ source
reads the other way round; the binary is ground truth.)"
  (let ((server->client (adnl-make-cipher (subseq nonce 0 32) (subseq nonce 64 80)))
        (client->server (adnl-make-cipher (subseq nonce 32 64) (subseq nonce 80 96))))
    (if initiator-p
        (values client->server server->client)
        (values server->client client->server))))

(defun build-init-packet (server-public &key (client-keypair (adnl-generate-keypair))
                                             (nonce (ironclad:random-data 160)))
  "Outbound handshake.  (VALUES packet256 tx-cipher rx-cipher)."
  (let* ((secret (adnl-shared-secret (keypair-secret client-keypair) server-public))
         (checksum (sha256 nonce)))
    (multiple-value-bind (key iv) (adnl-handshake-aes secret checksum)
      (let ((packet (%cat (adnl-short-id server-public)
                                   (keypair-public client-keypair)
                                   checksum
                                   (adnl-cipher-apply (adnl-make-cipher key iv) nonce))))
        (multiple-value-bind (tx rx) (adnl-session-ciphers nonce t)
          (values packet tx rx))))))

(defun decrypt-init-packet (packet server-keypair)
  "Inbound handshake.  PACKET is the 256 octets received.  Signals
ADNL-PROTOCOL-ERROR unless the destination id is ours and the nonce's
checksum verifies.  (VALUES tx-cipher rx-cipher client-public)."
  (unless (= (length packet) 256)
    (adnl-protocol-error "ADNL init packet must be 256 octets, got ~D" (length packet)))
  (unless (equalp (subseq packet 0 32) (adnl-short-id (keypair-public server-keypair)))
    (adnl-protocol-error "ADNL init packet addressed to another id"))
  (let* ((client-public (subseq packet 32 64))
         (checksum (subseq packet 64 96))
         (secret (adnl-shared-secret (keypair-secret server-keypair) client-public)))
    (multiple-value-bind (key iv) (adnl-handshake-aes secret checksum)
      (let ((nonce (adnl-cipher-apply (adnl-make-cipher key iv) (subseq packet 96 256))))
        (unless (equalp (sha256 nonce) checksum)
          (adnl-protocol-error "ADNL init packet checksum mismatch"))
        (multiple-value-bind (tx rx) (adnl-session-ciphers nonce nil)
          (values tx rx client-public))))))

;;; --- connections -----------------------------------------------------------

(defstruct (adnl-conn (:constructor %make-adnl-conn) (:copier nil))
  socket
  tx rx                                  ; ciphers (one continuous stream each)
  (send-lock (sb-thread:make-mutex :name "adnl send"))
  (buffer (make-array 0 :element-type '(unsigned-byte 8)))
  peer-public
  (closed-p nil))

(defun adnl-fd (conn) (sb-bsd-sockets:socket-file-descriptor (adnl-conn-socket conn)))

(defun adnl-socket-send-all (socket octets)
  (let ((sent 0) (n (length octets)) (buf (coerce octets '(simple-array (unsigned-byte 8) (*)))))
    (loop while (< sent n)
          do (let ((k (sb-bsd-sockets:socket-send socket (if (zerop sent) buf (subseq buf sent))
                                                  nil)))
               (when (or (null k) (<= k 0)) (error 'adnl-closed :format-control "send failed"))
               (incf sent k)))))

(defun adnl-conn-close (conn)
  (unless (adnl-conn-closed-p conn)
    (setf (adnl-conn-closed-p conn) t)
    (ignore-errors (sb-bsd-sockets:socket-close (adnl-conn-socket conn))))
  nil)

(defun adnl-read-exact (conn n deadline)
  "Read exactly N raw octets from CONN's socket.  DEADLINE is an internal-real-time
value or NIL.  Returns the octets, or :TIMEOUT when the deadline passes first
(nothing consumed is lost: partial data stays buffered).  EOF signals ADNL-CLOSED."
  (loop
    (let ((have (length (adnl-conn-buffer conn))))
      (when (>= have n)
        (let ((out (subseq (adnl-conn-buffer conn) 0 n)))
          (setf (adnl-conn-buffer conn) (subseq (adnl-conn-buffer conn) n))
          (return out))))
    (when (adnl-conn-closed-p conn) (error 'adnl-closed :format-control "connection closed"))
    (let ((remaining (and deadline
                          (/ (- deadline (get-internal-real-time)) internal-time-units-per-second))))
      (when (and remaining (<= remaining 0)) (return :timeout))
      (if (sb-sys:wait-until-fd-usable (adnl-fd conn) :input (or remaining 60))
          (let ((chunk (make-array 65536 :element-type '(unsigned-byte 8))))
            (multiple-value-bind (buf len)
                (handler-case (sb-bsd-sockets:socket-receive (adnl-conn-socket conn) chunk nil)
                  (error () (error 'adnl-closed :format-control "receive failed")))
              (declare (ignore buf))
              (when (or (null len) (zerop len))
                (error 'adnl-closed :format-control "peer closed the connection"))
              (setf (adnl-conn-buffer conn)
                    (%cat (adnl-conn-buffer conn) (subseq chunk 0 len)))))
          (when remaining (return :timeout))))))

(defun adnl-send-packet (conn payload)
  "Frame PAYLOAD on CONN's transmit stream and send it.  Thread-safe: the
lock spans encryption AND the socket write so frames never interleave."
  (sb-thread:with-mutex ((adnl-conn-send-lock conn))
    (adnl-socket-send-all (adnl-conn-socket conn) (adnl-encode-frame (adnl-conn-tx conn) payload))))

(defun adnl-recv-packet (conn &key (timeout nil))
  "Next verified payload, or :TIMEOUT.  Signals ADNL-PROTOCOL-ERROR on a bad
length or hash and ADNL-CLOSED on EOF."
  (let* ((deadline (and timeout (+ (get-internal-real-time)
                                   (round (* timeout internal-time-units-per-second)))))
         (head (adnl-read-exact conn 4 deadline)))
    (when (eq head :timeout) (return-from adnl-recv-packet :timeout))
    (let* ((len-plain (adnl-cipher-apply (adnl-conn-rx conn) head))
           (len (%le-octets->integer len-plain)))
      (adnl-check-frame-length len)
      ;; The length octets are already consumed from the keystream: the body
      ;; MUST be read to completion (a timeout mid-frame would desync the stream),
      ;; so give it a generous fixed budget instead of the caller's.
      (let ((body (adnl-read-exact conn len (+ (get-internal-real-time)
                                               (* 30 internal-time-units-per-second)))))
        (when (eq body :timeout) (adnl-protocol-error "timeout in the middle of a frame"))
        (adnl-verify-frame (adnl-cipher-apply (adnl-conn-rx conn) body))))))

(defun adnl-tcp-connect (host port &key (timeout 5))
  "Connect to HOST:PORT, giving up after TIMEOUT seconds (a host that silently drops SYNs would
otherwise hold the caller for the OS default of ~2 minutes).  The returned socket is blocking.
Failures signal ADNL-CLOSED whose text says \"refused\" / \"timed out\" / the OS error."
  (let ((socket (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
    (flet ((fail (why)
             (ignore-errors (sb-bsd-sockets:socket-close socket))
             (error 'adnl-closed :format-control "connect to ~A:~D failed: ~A"
                                 :format-arguments (list host port why))))
      (handler-case
          (progn
            (setf (sb-bsd-sockets:sockopt-tcp-nodelay socket) t)
            (setf (sb-bsd-sockets:non-blocking-mode socket) t)
            (let ((state (handler-case
                             (progn (sb-bsd-sockets:socket-connect
                                     socket (sb-bsd-sockets:make-inet-address host) port)
                                    :connected)
                           (sb-bsd-sockets:operation-in-progress () :in-progress))))
              (when (eq state :in-progress)
                (unless (sb-sys:wait-until-fd-usable
                         (sb-bsd-sockets:socket-file-descriptor socket) :output timeout)
                  (fail (format nil "timed out after ~As (no answer to the TCP SYN: filtered or unreachable)"
                                timeout)))
                ;; writable: connected, or failed -- the peer name only exists when connected
                (handler-case (sb-bsd-sockets:socket-peername socket)
                  (sb-bsd-sockets:not-connected-error ()
                    (fail "Connection refused (or reset) before the TCP handshake completed")))))
            (setf (sb-bsd-sockets:non-blocking-mode socket) nil)
            socket)
        (adnl-closed (e) (error e))
        (error (e) (fail e))))))

(defun adnl-connect (host port server-public &key (timeout 5) on-stage)
  "Outbound: connect, send the init packet, return an ADNL-CONN ready for
frames.  (The server's implicit ack -- an empty packet -- is consumed by the
first ADNL-RECV-PACKET the caller makes.)  ON-STAGE, when given, is called with
:TCP-CONNECTED after the TCP connection is up and :INIT-SENT after the 256-octet
init packet went out, so a caller can tell which step a failure belongs to."
  (let ((socket (adnl-tcp-connect host port :timeout timeout)))
    (when on-stage (funcall on-stage :tcp-connected))
    (multiple-value-bind (packet tx rx) (build-init-packet server-public)
      (handler-case (adnl-socket-send-all socket packet)
        (error (e) (ignore-errors (sb-bsd-sockets:socket-close socket)) (error e)))
      (when on-stage (funcall on-stage :init-sent))
      (%make-adnl-conn :socket socket :tx tx :rx rx :peer-public server-public))))

(defun adnl-accept-handshake (socket server-keypair &key (timeout 10))
  "Inbound: read the 256-octet init packet from the accepted SOCKET, install
the (reversed) ciphers and send the empty ack packet.  Returns the ADNL-CONN,
or signals ADNL-PROTOCOL-ERROR / ADNL-CLOSED (the caller closes the socket)."
  (let* ((tmp (%make-adnl-conn :socket socket))
         (packet (adnl-read-exact tmp 256 (+ (get-internal-real-time)
                                             (round (* timeout internal-time-units-per-second))))))
    (when (eq packet :timeout) (adnl-protocol-error "no init packet within ~As" timeout))
    (multiple-value-bind (tx rx client-public) (decrypt-init-packet packet server-keypair)
      (setf (adnl-conn-tx tmp) tx (adnl-conn-rx tmp) rx (adnl-conn-peer-public tmp) client-public)
      (adnl-send-packet tmp (make-array 0 :element-type '(unsigned-byte 8)))
      tmp)))
