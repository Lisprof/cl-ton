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

;;;; quic.lisp -- QUIC (RFC 9000/9001/9002), client side: the transport the TON node offers on its advertised
;;;; adnl.address.quic endpoints, meant to replace RLDP2 in the overlay path (src/overlay-query.lisp).
;;;;
;;;; The wire facts come from the RFCs and from the node's own stack (quic/ in the node sources): ngtcp2 with
;;;; OpenSSL TLS, ALPN "ton", and the TLS identity is the node's ADNL Ed25519 key, presented as a raw public key
;;;; (RFC 7250 cert types) with SNI <adnl-id hex>.adnl.  All cryptography is ironclad's, as everywhere else in
;;;; cl-ton; what lives here is protocol logic only.
;;;;
;;;; This file is built in layers, lowest first:
;;;;   * variable-length integers, HKDF and the TLS 1.3 label expansion QUIC borrows (RFC 9001 section 5.1);
;;;;   * packet protection keys, AEAD sealing/opening and header protection (RFC 9001 sections 5.2-5.4);
;;;;   * long-header packet assembly and disassembly, packet number encoding (RFC 9000 sections 17, A.2/A.3);
;;;;   * the Retry integrity tag (RFC 9001 section 5.8).
;;;; The TLS 1.3 handshake and the connection machinery (streams, ACKs, loss recovery) build on these.

(in-package :cl-ton)

;;; --- octets -------------------------------------------------------------------------------

(defun quic-octets (&rest bytes)
  (make-array (length bytes) :element-type '(unsigned-byte 8) :initial-contents bytes))

(defun quic-ascii (string)
  "The octets of an ASCII STRING."
  (map '(vector (unsigned-byte 8)) #'char-code string))

;;; --- variable-length integers (RFC 9000 section 16) ----------------------------------------

(defun quic-varint-length (value)
  "Octets needed to encode VALUE as a QUIC variable-length integer."
  (cond ((< value (ash 1 6)) 1)
        ((< value (ash 1 14)) 2)
        ((< value (ash 1 30)) 4)
        ((< value (ash 1 62)) 8)
        (t (error "QUIC varint too large: ~D" value))))

(defun quic-encode-varint (value &optional (size (quic-varint-length value)))
  "VALUE as a QUIC variable-length integer of exactly SIZE octets (SIZE defaults to the shortest form)."
  (let ((out (make-array size :element-type '(unsigned-byte 8)))
        (prefix (ecase size (1 0) (2 1) (4 2) (8 3))))
    (dotimes (i size)
      (setf (aref out (- size 1 i)) (ldb (byte 8 (* 8 i)) value)))
    (setf (ldb (byte 2 6) (aref out 0)) prefix)
    out))

(defun quic-decode-varint (octets &key (start 0))
  "Decode the varint at START in OCTETS.  Returns (VALUES value index-after)."
  (let* ((first (aref octets start))
         (size (ash 1 (ldb (byte 2 6) first)))
         (value (ldb (byte 6 0) first)))
    (dotimes (i (1- size))
      (setf value (logior (ash value 8) (aref octets (+ start 1 i)))))
    (values value (+ start size))))

;;; --- HKDF (RFC 5869) and the TLS 1.3 label expansion (RFC 8446 section 7.1) -----------------

(defun %hmac-sha256 (key data)
  (let ((h (ironclad:make-hmac key :sha256)))
    (ironclad:update-hmac h data)
    (ironclad:hmac-digest h)))

(defun hkdf-extract (salt ikm)
  "HKDF-Extract with SHA-256: HMAC(SALT, IKM); a zero salt of hash length stands in for a missing one."
  (%hmac-sha256 (or salt (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)) ikm))

(defun hkdf-expand (prk info length)
  "HKDF-Expand with SHA-256: LENGTH octets from PRK and INFO."
  (let ((out (make-array length :element-type '(unsigned-byte 8)))
        (previous (make-array 0 :element-type '(unsigned-byte 8)))
        (at 0)
        (counter 0))
    (loop while (< at length) do
      (incf counter)
      (setf previous (%hmac-sha256 prk (concat-octets (list previous info (quic-octets counter)))))
      (let ((take (min (length previous) (- length at))))
        (replace out previous :start1 at :end2 take)
        (incf at take)))
    out))

(defun hkdf-expand-label (secret label context length)
  "TLS 1.3 HKDF-Expand-Label: the HkdfLabel struct is uint16 LENGTH, \"tls13 \" + LABEL, CONTEXT."
  (let* ((full-label (concatenate 'string "tls13 " label))
         (info (concat-octets (list (uint->octets length 2)
                                     (quic-octets (length full-label))
                                     (quic-ascii full-label)
                                     (quic-octets (length context))
                                     context))))
    (hkdf-expand secret info length)))

;;; --- packet protection keys (RFC 9001 sections 5.1-5.3) -------------------------------------

(defstruct (quic-packet-keys (:conc-name quic-keys-))
  "One direction's packet protection material for one packet number space."
  (secret nil)                          ; the traffic secret these were derived from
  (key nil)                             ; AEAD key (16 octets for AES-128-GCM)
  (iv nil)                              ; 12 octets; the nonce is IV XOR packet number
  (hp nil))                             ; header protection key (16 octets for AES)

(defun quic-derive-keys (secret &key (key-length 16))
  "The (quic key, quic iv, quic hp) triple of a traffic SECRET."
  (make-quic-packet-keys
   :secret secret
   :key (hkdf-expand-label secret "quic key" #() key-length)
   :iv (hkdf-expand-label secret "quic iv" #() 12)
   :hp (hkdf-expand-label secret "quic hp" #() key-length)))

(defparameter +quic-initial-salt+
  (as-octets #(#x38 #x76 #x2c #xf7 #xf5 #x59 #x34 #xb3 #x4d #x17
               #x9a #xe6 #xa4 #xc8 #x0c #xad #xcc #xbb #x7f #x0a))
  "The QUIC v1 initial salt (RFC 9001 section 5.2).")

(defun quic-initial-secret (dcid)
  "HKDF-Extract of the version-1 initial salt over the client's chosen DCID."
  (hkdf-extract +quic-initial-salt+ dcid))

(defun quic-initial-keys (dcid role)
  "The Initial packet keys for ROLE (:CLIENT or :SERVER) of a connection whose client DCID is DCID."
  (let ((initial (quic-initial-secret dcid)))
    (quic-derive-keys (hkdf-expand-label initial (ecase role (:client "client in") (:server "server in")) #() 32))))

;;; --- AEAD and header protection (RFC 9001 sections 5.3-5.4) ---------------------------------

(defun quic-packet-nonce (keys packet-number)
  "The AEAD nonce for PACKET-NUMBER: the IV with the number XORed into its last 8 octets."
  (let ((nonce (copy-seq (quic-keys-iv keys))))
    (dotimes (i 8)
      (setf (aref nonce (- 11 i))
            (logxor (aref nonce (- 11 i)) (ldb (byte 8 (* 8 i)) packet-number))))
    nonce))

(defun quic-aead-seal (keys packet-number aad plaintext)
  "AES-128-GCM seal of PLAINTEXT under KEYS at PACKET-NUMBER with AAD; returns ciphertext || tag."
  (let ((cipher (ironclad:make-authenticated-encryption-mode
                 :gcm :cipher-name :aes :key (quic-keys-key keys)
                 :initialization-vector (quic-packet-nonce keys packet-number))))
    (let ((ct (ironclad:encrypt-message cipher plaintext :associated-data aad)))
      (concat-octets (list ct (ironclad:produce-tag cipher))))))

(defun quic-aead-open (keys packet-number aad ciphertext)
  "Inverse of QUIC-AEAD-SEAL; the plaintext, or NIL when the tag does not verify.
Ironclad's AEAD modes take the expected tag as an initarg rather than as part of the input,
so the trailing 16 octets are split off here."
  (handler-case
      (let* ((body-end (- (length ciphertext) 16))
             (cipher (ironclad:make-authenticated-encryption-mode
                      :gcm :cipher-name :aes :key (quic-keys-key keys)
                      :initialization-vector (quic-packet-nonce keys packet-number)
                      :tag (subseq ciphertext body-end))))
        (ironclad:decrypt-message cipher (subseq ciphertext 0 body-end) :associated-data aad))
    (error () nil)))

(defun quic-header-mask (keys sample)
  "The 5-octet header protection mask: AES-ECB of the 16-octet SAMPLE under the hp key (RFC 9001 section 5.4)."
  (let ((cipher (ironclad:make-cipher :aes :key (quic-keys-hp keys) :mode :ecb))
        (out (make-array 16 :element-type '(unsigned-byte 8))))
    (ironclad:encrypt cipher sample out)
    (subseq out 0 5)))

;;; --- packet numbers (RFC 9000 sections 17.1, A.2, A.3) ---------------------------------------

(defun quic-encode-packet-number (packet-number largest-acked)
  "Choose the shortest encoding of PACKET-NUMBER given the largest number the peer has acknowledged
(-1 when none): the count of unacknowledged packets decides, as in RFC 9000 section A.2.
Returns (VALUES truncated-value octet-count)."
  (let* ((unacked (if (minusp largest-acked) (1+ packet-number) (- packet-number largest-acked)))
         (bits (cond ((< unacked (ash 1 7)) 8)
                     ((< unacked (ash 1 15)) 16)
                     (t 32))))
    (values (ldb (byte bits 0) packet-number) (/ bits 8))))

(defun quic-decode-packet-number (truncated octet-count largest-received)
  "Recover the full packet number from its truncated wire form (RFC 9000 section A.3)."
  (let* ((bits (* 8 octet-count))
         (window (ash 1 bits))
         (half (/ window 2))
         (mask (1- window))
         (expected (1+ largest-received))
         (candidate (logior (logand expected (lognot mask)) truncated)))
    (cond ((<= candidate (- expected half)) (+ candidate window))
          ((and (> candidate (+ expected half)) (> candidate window)) (- candidate window))
          (t candidate))))

;;; --- long headers and packet protection (RFC 9000 section 17.2, RFC 9001 section 5.4) ---------

(defun quic-long-header-type (first-byte)
  "The long-header packet type of a first octet: :INITIAL, :ZERO-RTT, :HANDSHAKE or :RETRY."
  (ecase (ldb (byte 2 4) first-byte) (0 :initial) (1 :zero-rtt) (2 :handshake) (3 :retry)))

(defun quic-build-initial-header (dcid scid token length packet-number-length)
  "The unprotected header of an Initial packet, up to (not including) the packet number field.
LENGTH is the value of the Length field: packet number octets + payload + the 16-octet tag."
  (concat-octets (list (quic-octets (logior #xC0 (1- packet-number-length))) ; long form, type Initial, pn length bits
                       (uint->octets 1 4)                                    ; version 1
                       (quic-octets (length dcid)) dcid
                       (quic-octets (length scid)) scid
                       (quic-encode-varint (length token)) token
                       (quic-encode-varint length))))

(defun quic-protect-packet (keys header packet-number packet-number-length payload)
  "Protect one packet: HEADER is every header octet before the packet number field (for a long header it
already carries the Length field), PAYLOAD the frame octets.  Returns the protected packet."
  (let* ((pn-octets (uint->octets (ldb (byte (* 8 packet-number-length) 0) packet-number)
                                  packet-number-length))
         (aad (concat-octets (list header pn-octets)))
         (ciphertext (quic-aead-seal keys packet-number aad payload))
         ;; the sample is the ciphertext 4 octets past the start of the packet number field
         (sample-at (- 4 packet-number-length))
         (mask (quic-header-mask keys (subseq ciphertext sample-at (+ sample-at 16))))
         (packet (concat-octets (list aad ciphertext))))
    (setf (aref packet 0)
          (logxor (aref packet 0)
                  (logand (aref mask 0) (if (logbitp 7 (aref packet 0)) #x0F #x1F))))
    (dotimes (i packet-number-length)
      (setf (aref packet (+ (length header) i))
            (logxor (aref packet (+ (length header) i)) (aref mask (1+ i)))))
    packet))

(defun quic-parse-long-header (packet)
  "Parse a long header at the start of PACKET (header protection still applied).
Returns (VALUES type dcid scid index-of-length-field packet-end) where PACKET-END counts from the
packet start using the Length field, or NIL for a short header / Retry (no Length field)."
  (let ((first (aref packet 0)))
    (when (and (logbitp 7 first) (logbitp 6 first))
      (let* ((type (quic-long-header-type first))
             (at 1))
        (incf at 4)                             ; version
        (let ((dcid (subseq packet (1+ at) (+ at 1 (aref packet at)))))
          (incf at (1+ (length dcid)))
          (let ((scid (subseq packet (1+ at) (+ at 1 (aref packet at)))))
            (incf at (1+ (length scid)))
            (when (eq type :initial)            ; token
              (multiple-value-bind (token-length next) (quic-decode-varint packet :start at)
                (setf at (+ next token-length))))
            (if (eq type :retry)
                (values type dcid scid nil nil)
                (multiple-value-bind (length next) (quic-decode-varint packet :start at)
                  (values type dcid scid at (+ next length))))))))))

(defun quic-unprotect-packet (keys packet &key (largest-received -1))
  "Remove header and packet protection from a long-header PACKET under KEYS.
Returns (VALUES packet-number payload type) or NIL when the packet is malformed or fails authentication."
  (multiple-value-bind (type dcid scid length-at packet-end) (quic-parse-long-header packet)
    (declare (ignore dcid scid))
    (when (and type length-at (<= packet-end (length packet)))
      (multiple-value-bind (length pn-at) (quic-decode-varint packet :start length-at)
        (declare (ignore length))
        ;; the sample sits 4 octets into the protected payload, whatever the pn length
        (let* ((sample-at (+ pn-at 4))
               (mask (quic-header-mask keys (subseq packet sample-at (+ sample-at 16))))
               (first (logxor (aref packet 0) (logand (aref mask 0) #x0F)))
               (pn-length (1+ (ldb (byte 2 0) first)))
               (truncated 0))
          (dotimes (i pn-length)
            (setf truncated (logior (ash truncated 8)
                                    (logxor (aref packet (+ pn-at i)) (aref mask (1+ i))))))
          (let* ((pn (quic-decode-packet-number truncated pn-length largest-received))
                 (header (concat-octets (list (quic-octets first)
                                      (subseq packet 1 pn-at)
                                      (uint->octets truncated pn-length))))
                 (payload (quic-aead-open keys pn header
                                          (subseq packet (+ pn-at pn-length) packet-end))))
            (when payload
              (values pn payload type))))))))

;;; --- Retry integrity (RFC 9001 section 5.8) ---------------------------------------------------

(defparameter +quic-retry-key+
  (as-octets #(#xbe #x0c #x69 #x0b #x9f #x66 #x57 #x5a #x1d #x76 #x6b #x54 #xe3 #x68 #xc8 #x4e))
  "The fixed Retry integrity key of QUIC v1.")

(defparameter +quic-retry-nonce+
  (as-octets #(#x46 #x15 #x99 #xd3 #x5d #x63 #x2b #xf2 #x23 #x98 #x25 #xbb))
  "The fixed Retry integrity nonce of QUIC v1.")

(defun quic-retry-integrity-tag (retry-without-tag original-dcid)
  "The 16-octet integrity tag of a Retry packet: AES-128-GCM over the empty plaintext with the
packet (minus the tag) prefixed by the original DCID as associated data."
  (let ((cipher (ironclad:make-authenticated-encryption-mode
                 :gcm :cipher-name :aes :key +quic-retry-key+
                 :initialization-vector +quic-retry-nonce+))
        (aad (concat-octets (list (quic-octets (length original-dcid)) original-dcid retry-without-tag))))
    (ironclad:encrypt-message cipher #() :associated-data aad)
    (ironclad:produce-tag cipher)))

;;; --- TLS 1.3 (RFC 8446) as QUIC carries it (RFC 9001 section 4) ------------------------------
;;;
;;; A client-only TLS 1.3 handshake with the choices TON fixes: X25519 key exchange,
;;; TLS_AES_128_GCM_SHA256, ALPN "ton", and raw-public-key certificates (RFC 7250) in both
;;; directions -- the certificate is the peer's ADNL Ed25519 key as a SubjectPublicKeyInfo,
;;; and authentication is checking that it hashes (ADNL-SHORT-ID) to the id the DHT gave us.
;;; There is no record layer: handshake messages travel in CRYPTO frames, and the packet
;;; protection keys come from QUIC-DERIVE-KEYS over the traffic secrets, as in stage 1.

;;; -- byte-level helpers --

(defun tls-u16 (value) (uint->octets value 2))
(defun tls-u24 (value) (uint->octets value 3))

(defun tls-u16-at (octets at)
  (octets->uint octets :start at :end (+ at 2)))

(defun tls-u24-at (octets at)
  (octets->uint octets :start at :end (+ at 3)))

(defun tls-field (octets at nbytes)
  "The length-prefixed field at AT whose length is written on NBYTES octets.
Returns (VALUES field-octets index-after)."
  (let ((length (octets->uint octets :start at :end (+ at nbytes))))
    (values (subseq octets (+ at nbytes) (+ at nbytes length)) (+ at nbytes length))))

(defun tls-message (type body)
  "A handshake message: TYPE octet, 3-octet length, BODY."
  (concat-octets (list (quic-octets type) (tls-u24 (length body)) body)))

(defun tls-extension (type data)
  (concat-octets (list (tls-u16 type) (tls-u16 (length data)) data)))

(defun tls-parse-extensions (octets at end)
  "The extensions block OCTETS[AT,END) as an alist (type . data)."
  (let ((out '()))
    (loop while (< at end) do
      (let ((type (tls-u16-at octets at)))
        (multiple-value-bind (data next) (tls-field octets (+ at 2) 2)
          (push (cons type data) out)
          (setf at next))))
    (nreverse out)))

;;; -- the key schedule (RFC 8446 section 7.1) --

(defun tls-sha256 (octets)
  (ironclad:digest-sequence :sha256 octets))

(defparameter +tls-zero-32+ (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))
(defparameter +tls-empty-octets+ (make-array 0 :element-type '(unsigned-byte 8)))
(defparameter +tls-empty-hash+ (tls-sha256 +tls-empty-octets+)
  "SHA-256 of the empty string, the Hash(\"\") of the schedule's Derive-Secret steps.")

(defun tls-derive-secret (secret label transcript-hash)
  "Derive-Secret(secret, label, transcript-hash) with SHA-256."
  (hkdf-expand-label secret label transcript-hash 32))

(defun tls-early-secret ()
  "HKDF-Extract(0, 0): the early secret of a handshake without a PSK."
  (hkdf-extract +tls-zero-32+ +tls-zero-32+))

(defun tls-handshake-secret (ecdhe)
  "HKDF-Extract(Derive-Secret(early, \"derived\", Hash(\"\")), ECDHE)."
  (hkdf-extract (tls-derive-secret (tls-early-secret) "derived" +tls-empty-hash+) ecdhe))

(defun tls-master-secret (handshake-secret)
  "HKDF-Extract(Derive-Secret(handshake, \"derived\", Hash(\"\")), 0)."
  (hkdf-extract (tls-derive-secret handshake-secret "derived" +tls-empty-hash+) +tls-zero-32+))

(defun tls-finished-key (traffic-secret)
  (hkdf-expand-label traffic-secret "finished" #() 32))

(defun tls-verify-data (traffic-secret transcript-hash)
  "HMAC(finished_key, transcript-hash): the body of a Finished message."
  (%hmac-sha256 (tls-finished-key traffic-secret) transcript-hash))

;;; -- QUIC transport parameters (RFC 9000 section 18) --

(defun quic-encode-transport-parameters (params)
  "PARAMS is an alist (id . value); a value is an integer (varint-encoded) or an octet vector (raw)."
  (concat-octets
   (mapcar (lambda (p)
                   (let ((value (if (integerp (cdr p)) (quic-encode-varint (cdr p)) (cdr p))))
                     (concat-octets (list (quic-encode-varint (car p))
                                          (quic-encode-varint (length value))
                                          value))))
                 params)))

(defun quic-decode-transport-parameters (octets)
  "An alist (id . raw-value-octets)."
  (let ((out '()) (at 0))
    (loop while (< at (length octets)) do
      (multiple-value-bind (id next) (quic-decode-varint octets :start at)
        (multiple-value-bind (size after) (quic-decode-varint octets :start next)
          (push (cons id (subseq octets after (+ after size))) out)
          (setf at (+ after size)))))
    (nreverse out)))

(defun quic-tp-integer (params id &optional default)
  "The varint value of parameter ID in a decoded alist, or DEFAULT."
  (let ((cell (assoc id params)))
    (if cell (quic-decode-varint (cdr cell)) (or default 0))))

;;; -- raw public keys (RFC 7250): an Ed25519 key as SubjectPublicKeyInfo --

(defparameter +ed25519-spki-prefix+
  (as-octets #(#x30 #x2a #x30 #x05 #x06 #x03 #x2b #x65 #x70 #x03 #x21 #x00))
  "The fixed DER prefix of an Ed25519 SubjectPublicKeyInfo.")

(defun ed25519-spki (public-key)
  (concat-octets (list +ed25519-spki-prefix+ public-key)))

(defun spki-ed25519 (spki)
  "The Ed25519 public key inside an SPKI, or NIL when it is not one."
  (when (and (= (length spki) (+ (length +ed25519-spki-prefix+) 32))
             (equalp (subseq spki 0 (length +ed25519-spki-prefix+)) +ed25519-spki-prefix+))
    (subseq spki (length +ed25519-spki-prefix+))))

;;; -- the handshake state --

(defstruct (quic-tls (:conc-name qtls-) (:constructor %make-quic-tls))
  "One QUIC/TLS client handshake in progress.  Built by MAKE-QUIC-TLS, which fills in the
key share and the transport parameters."
  (sni nil)                             ; the peer's <adnl-id hex>.adnl name
  (expected-peer-id nil)                ; the ADNL short id the certificate key must hash to
  (dcid nil)                            ; our chosen destination connection id (the server's peer)
  (scid nil)                            ; our source connection id
  (identity-seed nil)                   ; our ADNL Ed25519 seed (the client certificate key)
  (identity-public nil)
  (x25519-private nil)
  (x25519-public nil)
  (transport-parameters nil)            ; our encoded transport parameters (the CH extension body)
  (messages '())                        ; the transcript: handshake messages, most recent first
  (handshake-secret nil)
  (client-hs-secret nil)
  (server-hs-secret nil)
  (master-secret nil)
  (client-ap-secret nil)
  (server-ap-secret nil)
  (server-parameters nil)               ; the server's decoded transport parameters
  (peer-public nil)                     ; the server's Ed25519 key, from its certificate
  (cert-requested nil)
  (cert-context nil)
  (done nil))

(defun qtls-add (state message)
  (push message (qtls-messages state)))

(defun qtls-transcript-hash (state)
  (tls-sha256 (concat-octets (reverse (qtls-messages state)))))

(defun make-quic-tls (&key sni expected-peer-id dcid scid identity-seed)
  "A fresh handshake state.  The transport parameters offer generous stream credit: a node
answers big queries (blocks) on the streams we open, and sends little on its own."
  (let* ((keypair (seed->keypair identity-seed))
         (xpriv (ironclad:random-data 32))
         (state (%make-quic-tls :sni sni :expected-peer-id expected-peer-id
                               :dcid dcid :scid scid
                               :identity-seed identity-seed
                               :identity-public (keypair-public keypair)
                               :x25519-private xpriv
                               :x25519-public (x25519 xpriv (concat-octets (list (quic-octets 9)
                                                                                 (make-array 31 :element-type '(unsigned-byte 8) :initial-element 0)))))))
    (setf (qtls-transport-parameters state)
          (quic-encode-transport-parameters
           (list (cons 1 0)             ; idle_timeout: disabled (a client on a poor link must not be timed out)
                 (cons 3 65527)         ; max_udp_payload_size
                 (cons 4 16777216)      ; initial_max_data
                 (cons 5 1048576)       ; initial_max_stream_data_bidi_local
                 (cons 6 1048576)       ; initial_max_stream_data_bidi_remote
                 (cons 7 1048576)       ; initial_max_stream_data_uni
                 (cons 8 16)            ; initial_max_streams_bidi
                 (cons 9 16)            ; initial_max_streams_uni
                 (cons 15 scid))))      ; initial_source_connection_id
    state))

;;; -- ClientHello --

(defun quic-tls-client-hello (state)
  "Build the ClientHello, record it in the transcript, and return the handshake message."
  (let* ((sni (qtls-sni state))
         (extensions
           (list
            (tls-extension 0                        ; server_name
                           (concat-octets (list (tls-u16 (+ 3 (length sni)))
                                                (quic-octets 0)
                                                (tls-u16 (length sni))
                                                (quic-ascii sni))))
            (tls-extension 10                       ; supported_groups: x25519
                           (concat-octets (list (tls-u16 2) (tls-u16 29))))
            (tls-extension 13                       ; signature_algorithms
                           (concat-octets (list (tls-u16 8)
                                                (tls-u16 #x0807)    ; ed25519
                                                (tls-u16 #x0403)    ; ecdsa_secp256r1_sha256
                                                (tls-u16 #x0804)    ; rsa_pss_rsae_sha256
                                                (tls-u16 #x0401)))) ; rsa_pkcs1_sha256
            (tls-extension 51                       ; key_share: our x25519 public
                           (concat-octets (list (tls-u16 (+ 4 (length (qtls-x25519-public state))))
                                                (tls-u16 29)
                                                (tls-u16 (length (qtls-x25519-public state)))
                                                (qtls-x25519-public state))))
            (tls-extension 43                       ; supported_versions: TLS 1.3
                           (concat-octets (list (quic-octets 2) (tls-u16 #x0304))))
            (tls-extension 45                       ; psk_key_exchange_modes: psk_dhe_ke
                           (quic-octets 1 1))
            (tls-extension 16                       ; ALPN: "ton"
                           (concat-octets (list (tls-u16 4) (quic-octets 3) (quic-ascii "ton"))))
            (tls-extension 20                       ; server_certificate_type (RFC 7250): raw public key
                           (concat-octets (list (quic-octets 1) (quic-octets 2))))
            (tls-extension 19                       ; client_certificate_type (RFC 7250): raw public key
                           (concat-octets (list (quic-octets 1) (quic-octets 2))))
            (tls-extension 57                       ; quic_transport_parameters
                           (qtls-transport-parameters state))))
         (ext-octets (concat-octets extensions))
         (body (concat-octets (list (tls-u16 #x0303)                ; legacy_version
                                    (ironclad:random-data 32)       ; random
                                    (quic-octets 0)                 ; legacy_session_id: empty
                                    (tls-u16 2) (tls-u16 #x1301)    ; cipher_suites: AES-128-GCM-SHA256
                                    (quic-octets 1 0)               ; legacy_compression_methods: null
                                    (tls-u16 (length ext-octets)) ext-octets)))
         (message (tls-message 1 body)))
    (qtls-add state message)
    message))

;;; -- ServerHello --

(defparameter +tls-hello-retry-random+
  (as-octets #(#xcf #x21 #xad #x74 #xe5 #x9a #x61 #x11 #xbe #x1d #x84 #x1f #x20 #x85 #x93 #x34
               #xa2 #x21 #x8a #xe0 #x41 #x24 #x45 #x8f #x06 #x11 #x22 #x58 #x8c #x79 #xe2 #x87))
  "The magic ServerHello.random that marks a HelloRetryRequest.")

(defun quic-tls-process-server-hello (state message)
  "Consume the ServerHello: agree the X25519 share, run the schedule to the handshake secrets,
and return (VALUES client-handshake-keys server-handshake-keys) for the Handshake packet space."
  (unless (= (aref message 0) 2) (ton-error "QUIC/TLS: expected ServerHello"))
  (let ((at 4))
    (setf at (+ at 2))                          ; legacy_version
    (let ((random (subseq message at (+ at 32))))
      (setf at (+ at 32))
      (when (equalp random +tls-hello-retry-random+)
        (ton-error "QUIC/TLS: server sent HelloRetryRequest (unsupported)"))
      (multiple-value-bind (session-id next) (tls-field message at 1)
        (declare (ignore session-id))
        (setf at next))
      (unless (= (tls-u16-at message at) #x1301)
        (ton-error "QUIC/TLS: server chose an unsupported cipher suite"))
      (setf at (+ at 3))                        ; cipher + legacy_compression_method
      (multiple-value-bind (block next) (tls-field message at 2)
        (setf at next)
        (let ((extensions (tls-parse-extensions block 0 (length block))))
          (unless (equalp (cdr (assoc 43 extensions)) (tls-u16 #x0304))
            (ton-error "QUIC/TLS: server did not negotiate TLS 1.3"))
          (let ((share (cdr (assoc 51 extensions))))
            (unless (and share (= (tls-u16-at share 0) 29))
              (ton-error "QUIC/TLS: server sent no x25519 key share"))
            (multiple-value-bind (server-public after) (tls-field share 2 2)
              (declare (ignore after))
              (let ((ecdhe (x25519 (qtls-x25519-private state) server-public)))
                (when (every #'zerop ecdhe)
                  (ton-error "QUIC/TLS: null X25519 shared secret"))
                (qtls-add state message)
                (let* ((hs (tls-handshake-secret ecdhe))
                       (hash (qtls-transcript-hash state)))
                  (setf (qtls-handshake-secret state) hs
                        (qtls-client-hs-secret state) (tls-derive-secret hs "c hs traffic" hash)
                        (qtls-server-hs-secret state) (tls-derive-secret hs "s hs traffic" hash))
                  (values (quic-derive-keys (qtls-client-hs-secret state))
                          (quic-derive-keys (qtls-server-hs-secret state))))))))))))

;;; -- the server's flight: EncryptedExtensions .. Finished --

(defun %qtls-encrypted-extensions (state message)
  (multiple-value-bind (block next) (tls-field message 4 2)
    (declare (ignore next))
    (let ((extensions (tls-parse-extensions block 0 (length block))))
      (let ((alpn (cdr (assoc 16 extensions))))
        (unless (and alpn (= (length alpn) 6) (equalp (subseq alpn 3) (quic-ascii "ton")))
          (ton-error "QUIC/TLS: server did not select ALPN \"ton\"")))
      (let ((cert-type (cdr (assoc 20 extensions))))
        (unless (and cert-type (= (aref cert-type 0) 2))
          (ton-error "QUIC/TLS: server did not agree a raw public key certificate")))
      (let ((tp (cdr (assoc 57 extensions))))
        (unless tp (ton-error "QUIC/TLS: server sent no transport parameters"))
        (let ((params (quic-decode-transport-parameters tp)))
          (unless (equalp (cdr (assoc 0 params)) (qtls-dcid state))
            (ton-error "QUIC/TLS: server transport parameters name another connection"))
          (setf (qtls-server-parameters state) params))))))

(defun %qtls-certificate-request (state message)
  (multiple-value-bind (context next) (tls-field message 4 1)
    (declare (ignore next))
    (setf (qtls-cert-requested state) t
          (qtls-cert-context state) context)))

(defun %qtls-certificate (state message)
  (qtls-add state message)
  (let ((at 4))
    (multiple-value-bind (context next) (tls-field message at 1)
      (declare (ignore context))
      (setf at next))
    (multiple-value-bind (list next) (tls-field message at 3)
      (setf at next)
      (multiple-value-bind (spki after) (tls-field list 0 3)
        (declare (ignore after))
        (let ((public (spki-ed25519 spki)))
          (unless public (ton-error "QUIC/TLS: server certificate is not an Ed25519 raw key"))
          (setf (qtls-peer-public state) public)
          (let ((expected (qtls-expected-peer-id state)))
            (when (and expected (not (equalp (adnl-short-id public) expected)))
              (ton-error "QUIC/TLS: server key does not hash to the expected ADNL id"))))))))

(defun %qtls-certificate-verify (state message)
  (let ((algorithm (tls-u16-at message 4)))
    (unless (= algorithm #x0807) (ton-error "QUIC/TLS: CertificateVerify is not Ed25519"))
    (multiple-value-bind (signature next) (tls-field message 6 2)
      (declare (ignore next))
      (let ((content (concat-octets (list (make-array 64 :element-type '(unsigned-byte 8) :initial-element #x20)
                                          (quic-ascii "TLS 1.3, server CertificateVerify")
                                          (quic-octets 0)
                                          (qtls-transcript-hash state)))))
        (unless (ironclad:verify-signature (ironclad:make-public-key :ed25519 :y (qtls-peer-public state))
                                           content signature)
          (ton-error "QUIC/TLS: CertificateVerify does not verify")))))
  (qtls-add state message))

(defun %qtls-finished (state message)
  (let ((expected (tls-verify-data (qtls-server-hs-secret state) (qtls-transcript-hash state))))
    (unless (equalp (subseq message 4) expected)
      (ton-error "QUIC/TLS: server Finished does not verify")))
  (qtls-add state message))

;;; -- our flight back, and the application secrets --

(defun %qtls-client-certificate (state)
  (let ((spki (ed25519-spki (qtls-identity-public state))))
    (tls-message 11 (concat-octets (list (quic-octets (length (qtls-cert-context state)))
                                         (qtls-cert-context state)
                                         (tls-u24 (+ 3 (length spki) 2))
                                         (tls-u24 (length spki)) spki
                                         (tls-u16 0))))))

(defun %qtls-client-certificate-verify (state)
  (let* ((content (concat-octets (list (make-array 64 :element-type '(unsigned-byte 8) :initial-element #x20)
                                       (quic-ascii "TLS 1.3, client CertificateVerify")
                                       (quic-octets 0)
                                       (qtls-transcript-hash state))))
         (signature (ironclad:sign-message (ironclad:make-private-key :ed25519 :x (qtls-identity-seed state))
                                           content)))
    (tls-message 15 (concat-octets (list (tls-u16 #x0807)
                                         (tls-u16 (length signature)) signature)))))

(defun quic-tls-process-flight (state messages)
  "Consume the server's handshake flight (EncryptedExtensions, an optional CertificateRequest,
Certificate, CertificateVerify, Finished -- whole messages, in order).  Verifies the raw-key
certificate against the expected ADNL id and both proofs of possession, then returns
(VALUES client-flight client-application-keys server-application-keys): the messages to send
back in the Handshake space (our Certificate and CertificateVerify when the server asked for
them, and our Finished) and the 1-RTT packet keys."
  (dolist (message messages)
    (ecase (aref message 0)
      (8 (qtls-add state message) (%qtls-encrypted-extensions state message))
      (13 (qtls-add state message) (%qtls-certificate-request state message))
      (11 (%qtls-certificate state message))
      (15 (%qtls-certificate-verify state message))
      (20 (%qtls-finished state message))
      (otherwise (ton-error "QUIC/TLS: unexpected handshake message type ~D" (aref message 0)))))
  (setf (qtls-master-secret state) (tls-master-secret (qtls-handshake-secret state)))
  (let ((hash (qtls-transcript-hash state)))
    (setf (qtls-client-ap-secret state) (tls-derive-secret (qtls-master-secret state) "c ap traffic" hash)
          (qtls-server-ap-secret state) (tls-derive-secret (qtls-master-secret state) "s ap traffic" hash)))
  (let ((flight '()))
    (when (qtls-cert-requested state)
      (let ((cert (%qtls-client-certificate state)))
        (qtls-add state cert) (push cert flight))
      (let ((cv (%qtls-client-certificate-verify state)))
        (qtls-add state cv) (push cv flight)))
    (push (tls-message 20 (tls-verify-data (qtls-client-hs-secret state) (qtls-transcript-hash state)))
          flight)
    (setf (qtls-done state) t)
    (values (nreverse flight)
            (quic-derive-keys (qtls-client-ap-secret state))
            (quic-derive-keys (qtls-server-ap-secret state)))))

;;; ================= Stage 3: the connection (RFC 9000/9002 transport) =============================
;;;
;;; A client connection in the pattern of RLDP.LISP: transport-neutral (a SEND function of one datagram),
;;; driven by QUIC-RECEIVE (from the socket's thread) and QUIC-TICK (from the caller's thread), with
;;; QUIC-QUERY as the blocking entry point.  Frames are handled for the client role: we open bidirectional
;;; streams for queries (one boxed quic.query, the boxed quic.answer back, each closed by FIN) and
;;; unidirectional streams for messages (boxed quic.message), exactly as the node's QuicSender does.

;;; --- stream reassembly: contiguous bytes plus an out-of-order stash -------------------------------

(defstruct (quic-reassembly (:conc-name qr-) (:copier nil))
  (buffer (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
  (stash (make-hash-table))             ; offset -> octets not yet contiguous
  (end 0))                              ; the buffer holds exactly the bytes [0, END)

(defun %quic-append (buffer octets)
  (dotimes (i (length octets)) (vector-push-extend (aref octets i) buffer))
  buffer)

(defun qr-feed (r offset data)
  "Feed DATA at stream OFFSET into R; returns T when the contiguous frontier advanced.
Duplicates and overlaps are absorbed: stream data is idempotent by offset."
  (let ((before (qr-end r)))
    (labels ((absorb (off dat)
               (cond ((> off (qr-end r))
                      (setf (gethash off (qr-stash r)) dat))
                     ((>= (+ off (length dat)) (qr-end r))
                      (let ((skip (- (qr-end r) off)))
                        (%quic-append (qr-buffer r) (subseq dat skip))
                        (setf (qr-end r) (+ (qr-end r) (- (length dat) skip)))))))
             (drain ()
               (loop for best = nil do
                 (maphash (lambda (k v) (declare (ignore v))
                            (when (and (<= k (qr-end r)) (or (null best) (< k best))) (setf best k)))
                          (qr-stash r))
                 (unless best (return))
                 (let ((dat (gethash best (qr-stash r))))
                   (remhash best (qr-stash r))
                   (absorb best dat)))))
      (absorb offset data)
      (drain))
    (> (qr-end r) before)))

;;; --- packet number spaces -------------------------------------------------------------------------

(defstruct (qsent (:conc-name qsent-) (:copier nil))
  "One sent packet, kept until it is acknowledged or declared lost."
  time ack-eliciting
  (crypto '())                          ; (offset . length) ranges of CRYPTO data it carried
  (streams '())                         ; (stream-id offset length) triples of STREAM data
  (fins '()))                           ; stream ids whose FIN it carried

(defstruct (quic-space (:conc-name qsp-) (:copier nil))
  "One packet number space: Initial, Handshake or Application."
  send-keys recv-keys
  (key-phase 0) (next-recv-keys nil) (prev-recv-keys nil) ; 1-RTT key updates (application space)
  (next-pn 0)
  (largest-received -1) (largest-received-time 0d0)
  (largest-acked -1)
  (received '())                        ; (low . high) packet ranges, highest first, for our ACKs
  (ack-needed nil) (ack-eliciting-since-ack 0)
  (sent (make-hash-table))              ; packet number -> QSENT
  (crypto-send (make-array 0 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))
  (crypto-send-next 0)                  ; first crypto offset never yet sent
  (crypto-resend '())                   ; (offset . length) ranges to retransmit
  (crypto-recv (make-quic-reassembly))
  (crypto-read 0)                       ; crypto bytes consumed by the handshake layer
  (probe nil))                          ; send a PING (and any resends) at the next flush

(defun %qsp-note-received (space pn now ack-eliciting)
  (setf (qsp-ack-needed space) (or (qsp-ack-needed space) ack-eliciting))
  (when ack-eliciting (incf (qsp-ack-eliciting-since-ack space)))
  (when (> pn (qsp-largest-received space))
    (setf (qsp-largest-received space) pn
          (qsp-largest-received-time space) now))
  (let ((lo pn) (hi pn) (kept '()))
    ;; merge PN into the range list (highest first), joining neighbours
    (dolist (r (qsp-received space))
      (if (and (<= (car r) (1+ hi)) (>= (cdr r) (1- lo)))
          (setf lo (min lo (car r)) hi (max hi (cdr r)))
          (push r kept)))
    (let ((all (sort (cons (cons lo hi) kept) #'> :key #'cdr)))
      (setf (qsp-received space) (subseq all 0 (min 16 (length all)))))))

(defun %qsp-ack-frame (space now exponent)
  "The ACK frame (type 0x02) for the space's received ranges, or NIL when there is nothing to ack."
  (when (qsp-received space)
    (let* ((ranges (qsp-received space))
           (largest (cdr (first ranges)))
           (delay-us (max 0 (round (* (- now (qsp-largest-received-time space)) 1000000)))))
      (concat-octets
       (append (list (quic-octets 2)
                     (quic-encode-varint largest)
                     (quic-encode-varint (ash delay-us (- exponent)))
                     (quic-encode-varint (1- (length ranges)))
                     (quic-encode-varint (- largest (car (first ranges)))))
               (loop for (prev cur) on ranges while cur append
                 (list (quic-encode-varint (- (car prev) (cdr cur) 2))   ; gap
                       (quic-encode-varint (- (cdr cur) (car cur)))))))))) ; range length

(defun %qsp-parse-ack (octets at)
  "Parse an ACK frame body after its type octet: returns (VALUES ranges delay next) with ranges as
(low . high), highest first; DELAY is the raw ACK Delay field."
  (multiple-value-bind (largest p1) (quic-decode-varint octets :start at)
    (multiple-value-bind (delay p2) (quic-decode-varint octets :start p1)
      (multiple-value-bind (count p3) (quic-decode-varint octets :start p2)
        (multiple-value-bind (first-range p4) (quic-decode-varint octets :start p3)
          (let ((ranges (list (cons (- largest first-range) largest))) (pos p4) (prev-low (- largest first-range)))
            (dotimes (i count)
              (multiple-value-bind (gap q1) (quic-decode-varint octets :start pos)
                (multiple-value-bind (len q2) (quic-decode-varint octets :start q1)
                  (let* ((hi (- prev-low gap 2)) (lo (- hi len)))
                    (push (cons lo hi) ranges)
                    (setf prev-low lo pos q2)))))
            (values (nreverse ranges) delay pos)))))))

(defun %qsp-note-acked (space ranges)
  "Remove the packets in RANGES from the sent table; returns the newly acked QSENT records."
  (let ((newly '()))
    (dolist (r ranges)
      (loop for pn from (car r) to (cdr r) do
        (let ((rec (gethash pn (qsp-sent space))))
          (when rec (push rec newly) (remhash pn (qsp-sent space))))))
    (when ranges (setf (qsp-largest-acked space) (max (qsp-largest-acked space) (cdr (first ranges)))))
    newly))

;;; --- streams --------------------------------------------------------------------------------------

(defstruct (quic-stream (:conc-name qs-) (:copier nil))
  id
  (send-data nil)                       ; the full octet vector to send
  (send-next 0)                         ; first offset never yet sent
  (resend '())                          ; (offset . length) ranges to retransmit
  (fin nil)                             ; close our side after the data
  (fin-sent nil) (fin-acked nil)
  (stopped nil)                         ; the peer sent STOP_SENDING
  (recv (make-quic-reassembly))
  (recv-fin nil) (recv-final-size nil)
  (delivered nil)                       ; the completed receive side was handed over once
  (reset nil))

(defun qs-bidirectional-p (stream) (zerop (logand (qs-id stream) 2)))
(defun qs-client-initiated-p (stream) (zerop (logand (qs-id stream) 1)))

(defstruct (quic-pending (:conc-name qpend-) (:copier nil))
  "One in-flight QUIC-QUERY, in the pattern of RLDP-PENDING."
  stream-id (semaphore (sb-thread:make-semaphore)) answer error (max-size 1048576) deadline)

(define-condition quic-timeout (ton-error) ()
  (:documentation "A QUIC query produced no answer in time."))

(define-condition quic-closed (ton-error) ()
  (:documentation "The QUIC connection closed (or failed) before the query was answered."))

;;; --- the connection -------------------------------------------------------------------------------

(defstruct (quic-connection (:conc-name qc-) (:constructor %make-quic-connection) (:copier nil))
  send                                  ; function of one datagram (octets)
  (lock (sb-thread:make-mutex :name "quic-connection"))
  (state :idle)                         ; :IDLE :HANDSHAKING :ESTABLISHED :CLOSED :FAILED
  tls                                   ; the QUIC-TLS handshake state
  dcid                                  ; the peer's current connection id (what we send as DCID)
  (dcid-seq 0)
  scid                                  ; our connection id (the peer sends it as DCID)
  original-dcid                         ; the DCID of our first Initial (for Retry validation)
  (token nil)                           ; a Retry token to present in Initial packets
  (peer-cids (make-hash-table))        ; sequence -> connection id, from NEW_CONNECTION_ID
  (retire-queue '())                    ; sequences to answer with RETIRE_CONNECTION_ID
  initial handshake app                 ; QUIC-SPACEs, NIL once discarded
  (streams (make-hash-table))          ; stream id -> QUIC-STREAM
  (next-stream-id 0)
  (pending (make-hash-table))          ; stream id -> QUIC-PENDING
  on-message                            ; function of the data octets of a quic.message, or NIL
  (peer-max-data 0) (peer-max-stream-bidi 0) (peer-max-stream-uni 0) (peer-max-streams-bidi 100)
  (ack-delay-exponent 3)
  (sent-stream-bytes 0)                 ; unique stream bytes sent, against PEER-MAX-DATA
  (srtt 0d0) (rttvar 0.125d0)           ; SRTT 0 = no sample yet
  (hs-flight '())                       ; the server's handshake messages after ServerHello
  (close-info nil)
  (handshake-done nil)
  (last-received 0d0))

(defun %qsp-declare-lost (space record conn)
  "A packet is lost: queue its payload for retransmission."
  (dolist (range (qsent-crypto record))
    (push range (qsp-crypto-resend space)))
  (dolist (triple (qsent-streams record))
    (let ((stream (gethash (first triple) (qc-streams conn))))
      (when stream (push (cons (second triple) (third triple)) (qs-resend stream)))))
  (dolist (id (qsent-fins record))
    (let ((stream (gethash id (qc-streams conn))))
      (when (and stream (not (qs-fin-acked stream))) (setf (qs-fin-sent stream) nil)))))


(defun quic-sni-of (peer-id)
  "The SNI name of a peer: the hex ADNL id, split in halves, under .adnl (quic-common.h)."
  (let ((hex (octets->hex peer-id)))
    (format nil "~A.~A.adnl" (subseq hex 0 32) (subseq hex 32))))

(defun make-quic-connection (send &key identity-seed peer-id scid dcid on-message)
  "A fresh client connection whose datagrams leave through SEND (a function of one octet vector).
PEER-ID is the server's ADNL short id: the TLS handshake is authenticated against it, and the SNI is
derived from it.  IDENTITY-SEED is our ADNL Ed25519 seed, presented as the client certificate when the
server asks.  SCID/DCID default to fresh random 8-octet ids.  Nothing is sent until QUIC-CONNECT."
  (let* ((scid (or scid (ironclad:random-data 8)))
         (dcid (or dcid (ironclad:random-data 8)))
         (tls (make-quic-tls :sni (and peer-id (quic-sni-of peer-id))
                             :expected-peer-id peer-id :dcid dcid :scid scid
                             :identity-seed identity-seed))
         (conn (%make-quic-connection :send send :tls tls :dcid dcid :scid scid
                                      :original-dcid dcid :on-message on-message))
         (initial (make-quic-space)))
    (setf (qsp-send-keys initial) (quic-initial-keys dcid :client)
          (qsp-recv-keys initial) (quic-initial-keys dcid :server)
          (qc-initial conn) initial)
    conn))

(defun %quic-connect (conn now)
  "Begin the handshake (the caller holds the lock): queue the ClientHello and send the first flight."
  (when (eq (qc-state conn) :idle)
    (setf (qc-state conn) :handshaking)
    (let ((hello (quic-tls-client-hello (qc-tls conn))))
      (%quic-append (qsp-crypto-send (qc-initial conn)) hello))
    (%quic-flush conn now)))

(defun quic-connect (conn &key (now (rldp-clock)))
  "Begin the handshake: queue the ClientHello in the Initial space and send the first flight."
  (sb-thread:with-mutex ((qc-lock conn)) (%quic-connect conn now))
  conn)

(defun %quic-fail (conn control &rest args)
  (setf (qc-state conn) :failed
        (qc-close-info conn) (apply #'format nil control args))
  (maphash (lambda (id pending)
             (declare (ignore id))
             (setf (qpend-error pending) (qc-close-info conn))
             (sb-thread:signal-semaphore (qpend-semaphore pending)))
           (qc-pending conn)))

(defun %quic-peer-limits (conn)
  "Adopt the server's transport parameters as our sending limits (called when its flight is verified)."
  (let ((params (qtls-server-parameters (qc-tls conn))))
    (setf (qc-peer-max-data conn) (quic-tp-integer params 4 0)
          (qc-peer-max-stream-bidi conn) (quic-tp-integer params 6 0)
          (qc-peer-max-stream-uni conn) (quic-tp-integer params 7 0)
          (qc-peer-max-streams-bidi conn) (quic-tp-integer params 8 100)
          (qc-ack-delay-exponent conn) (quic-tp-integer params 10 3))))

;;; --- sending: frame collection, packet building, flush --------------------------------------------

(defun %quic-build-long-header (type-bits dcid scid length pn-length)
  "A long header before the packet number field, for Handshake packets (Initial has its own builder)."
  (concat-octets (list (quic-octets (logior #xC0 (ash type-bits 4) (1- pn-length)))
                       (uint->octets 1 4)
                       (quic-octets (length dcid)) dcid
                       (quic-octets (length scid)) scid
                       (quic-encode-varint length))))

(defun %quic-space-frames (conn space kind now budget)
  "Collect the frames of one packet for SPACE out of CONN, at most BUDGET payload octets.
Returns (VALUES octets ack-eliciting crypto-ranges stream-triples fin-ids): the bookkeeping the caller
records for loss recovery.  Consumes what it packs (resend queues, send frontiers, the ACK debt)."
  (let ((parts '()) (used 0) (eliciting nil) (crypto '()) (streams '()) (fins '()))
    (labels ((%room () (- budget used))
             (emit (octets) (push octets parts) (incf used (length octets))))
      ;; ACK first (RFC 9000 19.3): never ack-eliciting itself
      (when (and (qsp-ack-needed space) (qsp-received space))
        (let ((frame (%qsp-ack-frame space now 3)))
          (when (and frame (<= (length frame) (%room)))
            (emit frame)
            (setf (qsp-ack-needed space) nil (qsp-ack-eliciting-since-ack space) 0))))
      ;; CRYPTO: retransmissions first, then fresh data
      (loop while (and (qsp-crypto-resend space) (> (%room) 8)) do
        (let* ((range (pop (qsp-crypto-resend space)))
               (take (min (cdr range) (- (%room) 8))))
          (when (> take 0)
            (emit (concat-octets (list (quic-octets 6) (quic-encode-varint (car range))
                                       (quic-encode-varint take)
                                       (subseq (qsp-crypto-send space) (car range) (+ (car range) take)))))
            (push (cons (car range) take) crypto)
            (setf eliciting t)
            (when (< take (cdr range))
              (push (cons (+ (car range) take) (- (cdr range) take)) (qsp-crypto-resend space))))))
      (loop while (and (< (qsp-crypto-send-next space) (length (qsp-crypto-send space))) (> (%room) 8)) do
        (let* ((off (qsp-crypto-send-next space))
               (take (min (- (length (qsp-crypto-send space)) off) (- (%room) 8))))
          (when (> take 0)
            (emit (concat-octets (list (quic-octets 6) (quic-encode-varint off)
                                       (quic-encode-varint take)
                                       (subseq (qsp-crypto-send space) off (+ off take)))))
            (push (cons off take) crypto)
            (setf (qsp-crypto-send-next space) (+ off take) eliciting t))))
      (when (eq kind :app)
        ;; RETIRE_CONNECTION_ID for ids the peer retired
        (loop while (and (qc-retire-queue conn) (> (%room) 4)) do
          (emit (concat-octets (list (quic-octets #x19) (quic-encode-varint (pop (qc-retire-queue conn))))))
          (setf eliciting t))
        ;; STREAM frames, lowest stream id first
        (let ((ids (sort (loop for id being the hash-keys of (qc-streams conn) collect id) #'<)))
          (dolist (id ids)
            (let ((stream (gethash id (qc-streams conn))))
              (when (and stream (not (qs-stopped stream)))
                (let ((limit (if (qs-bidirectional-p stream) (qc-peer-max-stream-bidi conn) (qc-peer-max-stream-uni conn))))
                  ;; retransmissions
                  (loop while (and (qs-resend stream) (> (%room) 12)) do
                    (let* ((range (pop (qs-resend stream)))
                           (take (min (cdr range) (- (%room) 12))))
                      (when (> take 0)
                        (emit (%quic-stream-frame stream (car range) take nil))
                        (push (list id (car range) take) streams)
                        (setf eliciting t)
                        (when (< take (cdr range))
                          (push (cons (+ (car range) take) (- (cdr range) take)) (qs-resend stream))))))
                  ;; fresh data, inside the flow-control limits
                  (loop while (and (qs-send-data stream) (< (qs-send-next stream) (length (qs-send-data stream)))
                                   (> (%room) 12)) do
                    (let* ((off (qs-send-next stream))
                           (allowed (min (- limit off)
                                         (- (qc-peer-max-data conn) (qc-sent-stream-bytes conn))
                                         (- (%room) 12))))
                      (when (<= allowed 0) (return))
                      (let ((take (min (- (length (qs-send-data stream)) off) allowed)))
                        (emit (%quic-stream-frame stream off take nil))
                        (push (list id off take) streams)
                        (setf (qs-send-next stream) (+ off take)
                              (qc-sent-stream-bytes conn) (+ (qc-sent-stream-bytes conn) take)
                              eliciting t))))
                  ;; FIN rides on an empty frame once everything is queued
                  (when (and (qs-fin stream) (not (qs-fin-sent stream))
                             (or (null (qs-send-data stream))
                                 (>= (qs-send-next stream) (length (qs-send-data stream))))
                             (> (%room) 4))
                    (emit (%quic-stream-frame stream (qs-send-next stream) 0 t))
                    (push id fins)
                    (setf (qs-fin-sent stream) t eliciting t))))))))
      ;; PING when probing for loss recovery
      (when (qsp-probe space)
        (when (> (%room) 0)
          (emit (quic-octets 1))
          (setf eliciting t))
        (setf (qsp-probe space) nil))
      (values (and parts (concat-octets (nreverse parts))) eliciting (nreverse crypto) (nreverse streams) (nreverse fins)))))

(defun %quic-stream-frame (stream offset length fin)
  (let ((type (logior #x08 (if (> offset 0) #x04 0) #x02 (if fin #x01 0))))
    (concat-octets (list (quic-octets type)
                         (quic-encode-varint (qs-id stream))
                         (when (> offset 0) (quic-encode-varint offset))
                         (quic-encode-varint length)
                         (if (> length 0)
                             (subseq (qs-send-data stream) offset (+ offset length))
                             (quic-octets))))))

(defun %quic-build-packet (conn space kind payload pn)
  "Protect PAYLOAD as packet PN of SPACE.  Returns the packet octets."
  (let* ((pn-length 4)
         (keys (qsp-send-keys space))
         (header (ecase kind
                   (:initial (quic-build-initial-header (qc-dcid conn) (qc-scid conn) (qc-token conn)
                                                        (+ pn-length (length payload) 16) pn-length))
                   (:handshake (%quic-build-long-header 2 (qc-dcid conn) (qc-scid conn)
                                                        (+ pn-length (length payload) 16) pn-length))
                   (:app (concat-octets (list (quic-octets (logior #x40 (ash (qsp-key-phase space) 2)
                                                                   (1- pn-length)))
                                              (qc-dcid conn)))))))
    (quic-protect-packet keys header pn pn-length payload)))

(defun %quic-flush (conn now)
  "Send every packet that is due, coalescing the spaces into datagrams of at most 1200 octets."
  (let ((parts '()) (total 0))
    (labels ((emit-datagram ()
               (when parts
                 (funcall (qc-send conn) (concat-octets (nreverse parts)))
                 (setf parts '() total 0))))
      (dolist (slot '(initial handshake app))
        (let ((space (slot-value conn slot)) (kind (intern (symbol-name slot) :keyword)))
          (when space
            (loop
              (let ((budget (- 1200 total 48)))
                (when (< budget 64) (emit-datagram) (setf budget (- 1200 48)))
                (multiple-value-bind (frames eliciting crypto streams fins)
                    (%quic-space-frames conn space kind now budget)
                  (unless frames (return))
                  (let* ((pn (qsp-next-pn space))
                         (packet (%quic-build-packet conn space kind frames pn)))
                    ;; a client Initial datagram is padded to 1200 octets (RFC 9000 14.1;
                    ;; servers discard smaller ones): pad the payload with PADDING and
                    ;; rebuild, sized by the real packet, never by a guessed header size
                    (when (and (eq kind :initial) (eq (qc-state conn) :handshaking)
                               (< (+ total (length packet)) 1200))
                      (setf frames (concat-octets
                                    (list frames
                                          (make-array (- 1200 total (length packet))
                                                      :element-type '(unsigned-byte 8) :initial-element 0)))
                            packet (%quic-build-packet conn space kind frames pn)))
                    (setf (qsp-next-pn space) (1+ pn))
                    (setf (gethash pn (qsp-sent space))
                          (make-qsent :time now :ack-eliciting eliciting :crypto crypto
                                      :streams streams :fins fins))
                    (push packet parts)
                    (incf total (length packet))
                    (when (>= total 1200) (emit-datagram)))))))))
      (emit-datagram)))
  conn)

(defun %quic-process-ack (conn space ranges delay-raw now)
  "Fold an ACK frame into SPACE: RTT sampling, loss declaration, FIN bookkeeping."
  (let ((newly (%qsp-note-acked space ranges)))
    (when newly
      (let ((best nil))
        (dolist (rec newly)
          (dolist (id (qsent-fins rec))
            (let ((stream (gethash id (qc-streams conn))))
              (when stream (setf (qs-fin-acked stream) t))))
          (when (and (qsent-ack-eliciting rec) (or (null best) (> (qsent-time rec) (qsent-time best))))
            (setf best rec)))
        (when best
          (let* ((delay (min (qsent-time best)
                             (/ (* delay-raw (expt 2 (qc-ack-delay-exponent conn))) 1000000d0)))
                 (latest (max 0d0 (- now (qsent-time best))))
                 (adjusted (max 0d0 (- latest delay))))
            (if (zerop (qsp-largest-acked space))
                (setf (qc-srtt conn) adjusted (qc-rttvar conn) (/ adjusted 2))
                (setf (qc-rttvar conn) (+ (* 0.75d0 (qc-rttvar conn))
                                          (* 0.25d0 (abs (- (qc-srtt conn) adjusted))))
                      (qc-srtt conn) (+ (* 0.875d0 (qc-srtt conn)) (* 0.125d0 adjusted)))))))
      ;; packet-threshold loss: three packets past an unacked one (RFC 9002 6.1)
      (let ((threshold (- (qsp-largest-acked space) 3)) (lost '()))
        (maphash (lambda (pn rec) (when (<= pn threshold) (push (cons pn rec) lost))) (qsp-sent space))
        (dolist (pair lost)
          (remhash (car pair) (qsp-sent space))
          (%qsp-declare-lost space (cdr pair) conn))))))

;;; --- receiving: packets, frames, the handshake driver ----------------------------------------------

(defun %quic-open-short (conn packet)
  "Open a 1-RTT packet.  Returns (VALUES packet-number payload) or NIL.
Handles a key update: a flipped phase bit makes us try the next generation of keys, and packets
that arrive late under the previous generation are still opened with the retired keys."
  (let* ((space (qc-app conn))
         (dcid-length (length (qc-scid conn)))
         (pn-at (1+ dcid-length))
         (sample-at (+ pn-at 4)))
    (when (and space (> (length packet) (+ pn-at 20)))
      (labels ((try (keys)
                 (let* ((mask (quic-header-mask keys (subseq packet sample-at (+ sample-at 16))))
                        (first (logxor (aref packet 0) (logand (aref mask 0) #x1F)))
                        (pn-length (1+ (ldb (byte 2 0) first)))
                        (truncated 0))
                   (dotimes (i pn-length)
                     (setf truncated (logior (ash truncated 8)
                                             (logxor (aref packet (+ pn-at i)) (aref mask (1+ i))))))
                   (let* ((pn (quic-decode-packet-number truncated pn-length (qsp-largest-received space)))
                          (header (concat-octets (list (quic-octets first) (subseq packet 1 pn-at)
                                                       (uint->octets truncated pn-length))))
                          (payload (quic-aead-open keys pn header (subseq packet (+ pn-at pn-length)))))
                     (when payload (values pn payload (ldb (byte 1 2) first)))))))
        (multiple-value-bind (pn payload phase) (try (qsp-recv-keys space))
          (declare (ignore phase))
          (when pn (return-from %quic-open-short (values pn payload)))
          (when (qsp-prev-recv-keys space)
            (multiple-value-bind (pn2 payload2) (try (qsp-prev-recv-keys space))
              (when pn2 (return-from %quic-open-short (values pn2 payload2)))))
          ;; a key update we have not seen yet: derive the next generation and adopt it on success
          (let ((next (quic-derive-keys (hkdf-expand-label (quic-keys-secret (qsp-recv-keys space))
                                                           "quic ku" #() 32))))
            (multiple-value-bind (pn3 payload3 phase3) (try next)
              (when pn3
                (setf (qsp-prev-recv-keys space) (qsp-recv-keys space)
                      (qsp-recv-keys space) next
                      (qsp-key-phase space) phase3)
                ;; our sending keys follow (RFC 9001 6.1)
                (setf (qsp-send-keys space)
                      (quic-derive-keys (hkdf-expand-label (quic-keys-secret (qsp-send-keys space))
                                                           "quic ku" #() 32)))
                (values pn3 payload3)))))))))

(defun %quic-stream (conn id)
  (or (gethash id (qc-streams conn))
      (setf (gethash id (qc-streams conn)) (make-quic-stream :id id))))

(defun %quic-stream-complete (conn stream)
  "A stream's receive side is complete: deliver a message, or answer a pending query."
  (let ((content (subseq (qr-buffer (qs-recv stream)) 0 (qs-recv-final-size stream))))
    (when (qs-client-initiated-p stream)
      (let ((pending (gethash (qs-id stream) (qc-pending conn))))
        (when pending
          (let ((obj (ignore-errors (tl-decode content))))
            (cond ((and obj (tl-is obj "quic.answer"))
                   (setf (qpend-answer pending) (coerce (tl-get obj :data) 'tl-octets)))
                  (t (setf (qpend-error pending) "the stream did not carry a quic.answer"))))
          (sb-thread:signal-semaphore (qpend-semaphore pending)))))
    (let ((obj (ignore-errors (tl-decode content))))
      (when (and obj (tl-is obj "quic.message") (qc-on-message conn))
        (funcall (qc-on-message conn) (coerce (tl-get obj :data) 'tl-octets))))))

(defun %quic-process-frames (conn space kind payload now)
  "Run one opened packet's frames.  Returns T when the packet carried anything ack-eliciting."
  (let ((at 0) (eliciting nil) (end (length payload)))
    (labels ((varint ()
               (multiple-value-bind (v next) (quic-decode-varint payload :start at)
                 (setf at next) v))
             (take (n) (prog1 (subseq payload at (+ at n)) (incf at n))))
      (loop while (< at end) do
        (let ((type (aref payload at)))
          (incf at)
          (cond
            ((= type 0))                ; PADDING
            ((= type 1) (setf eliciting t)) ; PING
            ((or (= type 2) (= type 3)) ; ACK (the ECN form 0x03 carries three more varints)
             (multiple-value-bind (ranges delay-raw next) (%qsp-parse-ack payload at)
               (setf at next)
               (when (= type 3) (varint) (varint) (varint))
               (%quic-process-ack conn space ranges delay-raw now)))
            (t (setf eliciting (or eliciting (not (member type '(2 3)))))
               (ecase type
                 (6                      ; CRYPTO
                  (let* ((offset (varint)) (len (varint)) (data (take len))
                         (before (qr-end (qsp-crypto-recv space))))
                    (qr-feed (qsp-crypto-recv space) offset data)
                    (when (> (qr-end (qsp-crypto-recv space)) before)
                      (%quic-crypto-advanced conn space kind))))
                 ((8 9 10 11 12 13 14 15) ; STREAM (offset/length/fin bits in the low nibble)
                  (let* ((id (varint))
                         (offset (if (logbitp 2 type) (varint) 0))
                         (len (if (logbitp 1 type) (varint) (- end at)))
                         (data (take len))
                         (fin (logbitp 0 type))
                         (stream (%quic-stream conn id)))
                    (qr-feed (qs-recv stream) offset data)
                    (when fin
                      (setf (qs-recv-fin stream) t
                            (qs-recv-final-size stream) (+ offset (length data))))
                    (when (and (qs-recv-fin stream) (qs-recv-final-size stream)
                               (>= (qr-end (qs-recv stream)) (qs-recv-final-size stream))
                               (not (qs-reset stream)) (not (qs-delivered stream)))
                      (setf (qs-delivered stream) t)
                      (%quic-stream-complete conn stream))))
                 (4                      ; RESET_STREAM
                  (let* ((id (varint)) (code (varint)) (final (varint)) (stream (%quic-stream conn id)))
                    (declare (ignore code final))
                    (setf (qs-reset stream) t)
                    (let ((pending (gethash id (qc-pending conn))))
                      (when pending
                        (setf (qpend-error pending) "the peer reset the stream")
                        (sb-thread:signal-semaphore (qpend-semaphore pending))))))
                 (5                      ; STOP_SENDING
                  (let* ((id (varint)) (code (varint)) (stream (%quic-stream conn id)))
                    (declare (ignore code))
                    (setf (qs-stopped stream) t)))
                 (16                     ; MAX_DATA
                  (setf (qc-peer-max-data conn) (max (qc-peer-max-data conn) (varint))))
                 (17                     ; MAX_STREAM_DATA
                  (let ((id (varint)) (maximum (varint)))
                    (declare (ignore id maximum)))) ; our streams are client-opened; the TP value governs
                 (18                     ; MAX_STREAMS (bidi)
                  (setf (qc-peer-max-streams-bidi conn) (max (qc-peer-max-streams-bidi conn) (varint))))
                 (19 (varint))           ; MAX_STREAMS (uni)
                 (20 (varint))           ; DATA_BLOCKED
                 (21 (varint) (varint))  ; STREAM_DATA_BLOCKED
                 (22 (varint))           ; STREAMS_BLOCKED (bidi)
                 (23 (varint))           ; STREAMS_BLOCKED (uni)
                 (24                     ; NEW_CONNECTION_ID
                  (let* ((seq (varint)) (retire (varint))
                         (cid-len (prog1 (aref payload at) (incf at)))
                         (cid (take cid-len)))
                    (take 16)           ; the stateless reset token; we never reset, so it is not kept
                    (setf (gethash seq (qc-peer-cids conn)) cid)
                    (loop for s from 0 below retire do (pushnew s (qc-retire-queue conn)))
                    (when (and (>= retire (qc-dcid-seq conn)) (gethash seq (qc-peer-cids conn)) (> seq (qc-dcid-seq conn)))
                      (setf (qc-dcid conn) cid (qc-dcid-seq conn) seq))))
                 (25                     ; RETIRE_CONNECTION_ID
                  (varint))
                 (26 (take 8))           ; PATH_CHALLENGE (we do not migrate; no response needed as client of a fixed peer)
                 (27 (take 8))           ; PATH_RESPONSE
                 (28                     ; CONNECTION_CLOSE (transport)
                  (let* ((code (varint)) (frame-type (varint))
                         (reason-len (varint)) (reason (take reason-len)))
                    (declare (ignore code frame-type))
                    (%quic-fail conn "connection closed by the peer: ~A"
                                (or (ignore-errors (babel:octets-to-string reason)) ""))
                    (return-from %quic-process-frames eliciting)))
                 (29                     ; CONNECTION_CLOSE (application)
                  (let* ((code (varint)) (reason-len (varint)) (reason (take reason-len)))
                    (declare (ignore code))
                    (%quic-fail conn "connection closed by the peer (application): ~A"
                                (or (ignore-errors (babel:octets-to-string reason)) ""))
                    (return-from %quic-process-frames eliciting)))
                 (30                     ; HANDSHAKE_DONE
                  (setf (qc-handshake-done conn) t)
                  (when (qc-handshake conn) (setf (qc-handshake conn) nil))) ; discard Handshake keys
                 (7                      ; NEW_TOKEN
                  (let ((len (varint))) (take len)))))))))
    eliciting))

(defun %quic-take-crypto-message (space)
  "The next complete handshake message in SPACE's crypto stream, or NIL."
  (let* ((buffer (qr-buffer (qsp-crypto-recv space)))
         (at (qsp-crypto-read space))
         (avail (- (qr-end (qsp-crypto-recv space)) at)))
    (when (>= avail 4)
      (let ((len (tls-u24-at buffer (+ at 1))))
        (when (>= avail (+ 4 len))
          (setf (qsp-crypto-read space) (+ at 4 len))
          (subseq buffer at (+ at 4 len)))))))

(defun %quic-crypto-advanced (conn space kind)
  "New contiguous crypto bytes arrived in SPACE: drive the TLS handshake with them."
  (ecase kind
    (:initial
     (loop for message = (%quic-take-crypto-message space) while message do
       (when (and (= (aref message 0) 2) (not (qc-handshake conn))) ; ServerHello
         (multiple-value-bind (send-keys recv-keys)
             (quic-tls-process-server-hello (qc-tls conn) message)
           (let ((hs (make-quic-space)))
             (setf (qsp-send-keys hs) send-keys (qsp-recv-keys hs) recv-keys
                   (qc-handshake conn) hs))))))
    (:handshake
     (loop for message = (%quic-take-crypto-message space) while message do
       (push message (qc-hs-flight conn))
       (when (and (= (aref message 0) 20) (eq (qc-state conn) :handshaking)) ; Finished: the flight is complete
         (let ((flight (quic-tls-process-flight (qc-tls conn) (nreverse (qc-hs-flight conn)))))
           (setf (qc-hs-flight conn) '())
           (%quic-append (qsp-crypto-send space) (concat-octets flight))
           (let ((app (make-quic-space)))
             (setf (qsp-send-keys app) (quic-derive-keys (qtls-client-ap-secret (qc-tls conn)))
                   (qsp-recv-keys app) (quic-derive-keys (qtls-server-ap-secret (qc-tls conn)))
                   (qc-app conn) app))
           (%quic-peer-limits conn)
           (setf (qc-state conn) :established)
           ;; Initial keys are discarded once the handshake keys have been used (RFC 9001 4.10)
           (setf (qc-initial conn) nil)))))
    (:app nil)))

(defun %quic-retry (conn packet now)
  "A Retry packet: validate it, adopt the server's connection id and token, restart the Initial flight."
  (multiple-value-bind (type dcid scid) (quic-parse-long-header packet)
    (declare (ignore type))
    (when (and (equalp dcid (qc-scid conn))
               (> (length packet) 16)
               (equalp (subseq packet (- (length packet) 16))
                       (quic-retry-integrity-tag (subseq packet 0 (- (length packet) 16))
                                                 (qc-original-dcid conn))))
      (let* ((header-end (+ 1 4 1 (length dcid) 1 (length scid)))
             (token (subseq packet header-end (- (length packet) 16)))
             (initial (make-quic-space)))
        (setf (qc-dcid conn) scid (qc-token conn) token)
        (setf (qsp-send-keys initial) (quic-initial-keys scid :client)
              (qsp-recv-keys initial) (quic-initial-keys scid :server))
        ;; the ClientHello bytes are resent verbatim under the new keys (the transcript is unchanged)
        (%quic-append (qsp-crypto-send initial)
                      (subseq (qsp-crypto-send (qc-initial conn)) 0 (length (qsp-crypto-send (qc-initial conn)))))
        (setf (qc-initial conn) initial)
        (%quic-flush conn now)))))

(defun quic-receive (conn datagram &key (now (rldp-clock)))
  "Feed one received DATAGRAM (one UDP payload, possibly several coalesced packets) into CONN."
  (sb-thread:with-mutex ((qc-lock conn))
    (unless (member (qc-state conn) '(:closed :failed))
      (setf (qc-last-received conn) now)
      (let ((at 0))
        (loop while (< at (length datagram)) do
          (let ((first (aref datagram at)))
            (cond
              ((logbitp 7 first)        ; long header
               (let ((packet (subseq datagram at)))
                 (when (< (length packet) 5) (return))
                 (let ((version (octets->uint packet :start 1 :end 5)))
                   (cond
                     ((zerop version)   ; version negotiation: we only speak v1
                      (%quic-fail conn "the peer does not speak QUIC version 1")
                      (return))
                     ((eq (quic-long-header-type first) :retry)
                      (%quic-retry conn packet now)
                      (return))
                     (t
                      (multiple-value-bind (type dcid scid length-at packet-end)
                          (quic-parse-long-header packet)
                        (declare (ignore length-at))
                        (when (or (null type) (null packet-end) (> packet-end (length packet)))
                          (return))
                        (let ((one (subseq packet 0 packet-end))
                              (space (ecase type
                                       (:initial (qc-initial conn))
                                       (:handshake (qc-handshake conn))
                                       (:zero-rtt nil))))
                          (when (and space (equalp dcid (qc-scid conn)))
                            (multiple-value-bind (pn payload)
                                (quic-unprotect-packet (qsp-recv-keys space) one
                                                       :largest-received (qsp-largest-received space))
                              (when pn
                                (when (eq type :initial)
                                  (setf (qc-dcid conn) scid)) ; adopt the server's chosen id
                                (let ((eliciting
                                        (handler-case
                                            (%quic-process-frames
                                             conn space
                                             (ecase type (:initial :initial) (:handshake :handshake))
                                             payload now)
                                          (ton-error (e)
                                            (%quic-fail conn "handshake failed: ~A" e)
                                            nil))))
                                  (%qsp-note-received space pn now eliciting))))))
                        (setf at (+ at packet-end))))))))
              (t                        ; short header: the rest of the datagram
               (let ((packet (subseq datagram at)))
                 (multiple-value-bind (pn payload) (%quic-open-short conn packet)
                   (when pn
                     (let ((eliciting
                             (handler-case (%quic-process-frames conn (qc-app conn) :app payload now)
                               (ton-error (e)
                                 (%quic-fail conn "~A" e)
                                 nil))))
                       (%qsp-note-received (qc-app conn) pn now eliciting))))
                 (setf at (length datagram))))))))))
  conn)

(defun quic-tick (conn &optional (now (rldp-clock)))
  "Drive CONN at time NOW: loss timers, ACK timers, retransmission.  Returns the next time it wants
to be called, or NIL.  Incoming datagrams arrive through QUIC-RECEIVE from the transport's thread."
  (sb-thread:with-mutex ((qc-lock conn))
    (unless (member (qc-state conn) '(:closed :failed :idle))
      (let ((wake nil))
        (labels ((note (time) (when time (setf wake (if wake (min wake time) time)))))
          (dolist (space (list (qc-initial conn) (qc-handshake conn) (qc-app conn)))
            (when space
              ;; probe timeout: the oldest unacked ack-eliciting packet is too old -- resend its
              ;; payload as lost and probe with a PING (RFC 9002 6.2, simplified)
              (let ((oldest nil) (oldest-pn nil) (pto (+ (qc-srtt conn) (* 4 (qc-rttvar conn)) 0.025d0)))
                (maphash (lambda (pn rec)
                           (when (and (qsent-ack-eliciting rec)
                                      (or (null oldest) (< (qsent-time rec) (qsent-time oldest))))
                             (setf oldest rec oldest-pn pn)))
                         (qsp-sent space))
                (when oldest
                  (if (> (- now (qsent-time oldest)) pto)
                      (progn (remhash oldest-pn (qsp-sent space))
                             (%qsp-declare-lost space oldest conn)
                             (setf (qsp-probe space) t))
                      (note (+ (qsent-time oldest) pto)))))
              ;; ACK timer: an unacked ack-eliciting packet waits at most ~25 ms for its ACK;
              ;; the flush below sends a due ACK, this only schedules the wake-up
              (when (and (qsp-ack-needed space) (> (qsp-ack-eliciting-since-ack space) 0))
                (note (+ (qsp-largest-received-time space) 0.025d0)))))
          (%quic-flush conn now)
          ;; a flush may still owe data (budget or flow control): come back soon
          (dolist (space (list (qc-initial conn) (qc-handshake conn) (qc-app conn)))
            (when (and space (or (qsp-crypto-resend space)
                                 (< (qsp-crypto-send-next space) (length (qsp-crypto-send space)))
                                 (qsp-probe space)))
              (note (+ now 0.001d0))))
          (dolist (stream (loop for s being the hash-values of (qc-streams conn) collect s))
            (when (or (qs-resend stream)
                      (and (qs-send-data stream) (< (qs-send-next stream) (length (qs-send-data stream))))
                      (and (qs-fin stream) (not (qs-fin-sent stream))))
              (note (+ now 0.001d0))))
          wake)))))

;;; --- the application interface ----------------------------------------------------------------------

(defun %quic-open-stream (conn bidi)
  "The next client stream: bidirectional ids are 0, 4, 8..., unidirectional 2, 6, 10...."
  (let* ((base (qc-next-stream-id conn))
         (stream (make-quic-stream :id (if bidi base (+ base 2)))))
    (setf (qc-next-stream-id conn) (+ base 4)
          (gethash (qs-id stream) (qc-streams conn)) stream)
    stream))

(defun quic-query-start (conn data &key (timeout 5) (max-answer-size 1048576) (now (rldp-clock)))
  "Open a stream, send DATA as a boxed quic.query and close our side; returns the pending record.
DATA is the framed query itself (for example OVERLAY-QUERY-BYTES output)."
  (sb-thread:with-mutex ((qc-lock conn))
    (%quic-connect conn now)
    (let* ((stream (%quic-open-stream conn t))
           (pending (make-quic-pending :stream-id (qs-id stream) :max-size max-answer-size
                                       :deadline (+ now timeout))))
      (setf (qs-send-data stream)
            (tl-encode (tl-make "quic.query" :data (coerce data 'tl-octets)))
            (qs-fin stream) t
            (gethash (qs-id stream) (qc-pending conn)) pending)
      (%quic-flush conn now)
      pending)))

(defun quic-pending-answer (pending) (qpend-answer pending))

(defun quic-query-cancel (conn pending)
  (sb-thread:with-mutex ((qc-lock conn))
    (remhash (qpend-stream-id pending) (qc-pending conn))))

(defun quic-query (conn data &key (timeout 5) (max-answer-size 1048576))
  "Run the query DATA over CONN and return the answer octets (the data of the boxed quic.answer);
signals QUIC-TIMEOUT after TIMEOUT seconds, QUIC-CLOSED when the connection dies first.
The calling thread drives the connection's clock while it waits, as with RLDP-QUERY."
  (let* ((start (rldp-clock)) (deadline (+ start timeout))
         (pending (quic-query-start conn data :timeout timeout :max-answer-size max-answer-size :now start)))
    (unwind-protect
         (loop
           (let* ((now (rldp-clock)) (left (- deadline now)))
             (when (qpend-answer pending) (return (qpend-answer pending)))
             (when (qpend-error pending)
               (error 'quic-closed :format-control "QUIC query: ~A" :format-arguments (list (qpend-error pending))))
             (when (<= left 0)
               (error 'quic-timeout :format-control "QUIC query: no answer in ~As" :format-arguments (list timeout)))
             (let ((wake (quic-tick conn now)))
               (when (sb-thread:wait-on-semaphore (qpend-semaphore pending)
                                                  :timeout (max 0.0005d0 (min left 0.05d0 (if wake (- wake now) 0.05d0))))
                 (when (qpend-answer pending) (return (qpend-answer pending)))))))
      (quic-query-cancel conn pending))))

(defun quic-send-message (conn data &key (now (rldp-clock)))
  "Send DATA as a boxed quic.message on a fresh unidirectional stream (fire and forget, as ADNL messages are)."
  (sb-thread:with-mutex ((qc-lock conn))
    (%quic-connect conn now)
    (let ((stream (%quic-open-stream conn nil)))
      (setf (qs-send-data stream)
            (tl-encode (tl-make "quic.message" :data (coerce data 'tl-octets)))
            (qs-fin stream) t)
      (%quic-flush conn now)))
  t)
