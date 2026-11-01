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

;;;; adnl-udp.lisp -- ADNL over UDP: datagrams, signed packets, queries.
;;;;
;;;; Written from the node's own sources (adnl/adnl-peer.cpp, adnl-packet.cpp, keys/encryptor.cpp):
;;;;
;;;;   datagram = DST(32)  ||  EPHEMERAL-PUBLIC(32) || SHA256(PLAIN)(32) || AES-256-CTR(PLAIN)
;;;;   DST      = the short id (sha256 of the boxed pub.ed25519) of the node the datagram is for
;;;;   secret   = X25519 of the sender's EPHEMERAL key and the receiver's key (as in the TCP handshake)
;;;;   key      = secret[0..16] || digest[16..32]        iv = digest[0..4] || secret[20..32]
;;;;   PLAIN    = a boxed adnl.packetContents: the sender's key, a SIGNATURE over the packet without the signature
;;;;              (and its flag), seqno / confirm_seqno, reinit dates, an address list, and the messages
;;;;
;;;; The first packet to a peer carries an address list with NO address and a version other than -1: the peer then
;;;; takes the datagram's source address as ours ("implicit address"), which is how a client with no public address
;;;; is answered.
;;;;
;;;; CHANNELS (adnl/adnl-channel.cpp, adnl-peer.cpp): each side makes a channel Ed25519 key and sends adnl.message.createChannel
;;;; {its public key, date}; the other answers adnl.message.confirmChannel {its key, the sender's key, date}.  With
;;;; shared = X25519(own channel key, peer's channel key) and rev = shared reversed byte for byte, the node whose short id
;;;; is the SMALLER takes IN = shared, OUT = rev, the other IN = rev, OUT = shared (equal ids: both shared).  A channel id is the
;;;; sha256 of the boxed pub.aes key; a channel datagram is OUT-id (32) || sha256(plain) (32) || AES-CTR(plain) with
;;;; key = OUT[0..16]||digest[16..32] and iv = digest[0..4]||OUT[20..32]; the plain packet carries only seqno, confirm_seqno
;;;; and messages (the channel authenticates it: no key, no signature).  A side sends through the channel once it has the
;;;; peer's confirmChannel (or a first channel packet from the peer); before that every packet is signed and carries the
;;;; channel message.
;;;;
;;;; PARTS: a message whose serialization exceeds 1024+128 octets is sent as adnl.message.part {sha256 of the boxed message,
;;;; total size, offset, up to 1024 octets}; the receiver takes the parts in order, checks the hash and decodes the message;
;;;; nothing bigger than 8192+128 octets is accepted.  A datagram is at most 1440 octets.

(in-package :cl-ton)

(define-condition adnl-udp-timeout (ton-error) ())

(defconstant +adnl-udp-max-datagram+ 1440
  "The MTU of the node's network manager (adnl/adnl-network-manager.h).")
(defconstant +adnl-udp-part-size+ 1024 "Adnl::get_mtu(): the largest part of a big message.")
(defconstant +adnl-udp-max-message+ (+ 8192 128) "Adnl::huge_packet_max_size() + 128.")

;;; --- the encrypted message --------------------------------------------------------------------------------------------------------

(defun adnl-udp-key-iv (secret digest)
  "(VALUES key32 iv16) of an ADNL message: the shared SECRET and the sha256 DIGEST of the plain text."
  (values (%cat (subseq secret 0 16) (subseq digest 16 32))
          (%cat (subseq digest 0 4) (subseq secret 20 32))))

(defun adnl-udp-encrypt (peer-public plain &optional (ephemeral (adnl-generate-keypair)))
  "PLAIN encrypted to the ed25519 key PEER-PUBLIC: ephemeral public key (32) || digest (32) || ciphertext."
  (let* ((plain (as-octets plain))
         (secret (adnl-shared-secret (keypair-secret ephemeral) peer-public))
         (digest (sha256 plain)))
    (multiple-value-bind (key iv) (adnl-udp-key-iv secret digest)
      (%cat (keypair-public ephemeral) digest (adnl-cipher-apply (adnl-make-cipher key iv) plain)))))

(defun adnl-udp-decrypt (keypair message)
  "The plain text of MESSAGE (what ADNL-UDP-ENCRYPT made) for the owner of KEYPAIR; signals on a message that is
too short or whose digest does not match what the keys decrypt to."
  (when (< (length message) 64)
    (adnl-protocol-error "ADNL UDP message too short (~D octets)" (length message)))
  (let* ((public (subseq message 0 32))
         (digest (subseq message 32 64))
         (secret (adnl-shared-secret (keypair-secret keypair) public)))
    (multiple-value-bind (key iv) (adnl-udp-key-iv secret digest)
      (let ((plain (adnl-cipher-apply (adnl-make-cipher key iv) (subseq message 64))))
        (unless (equalp (sha256 plain) digest)
          (adnl-protocol-error "ADNL UDP message: sha256 mismatch after decryption"))
        plain))))

(defun adnl-udp-datagram (peer-public plain &optional (ephemeral (adnl-generate-keypair)))
  "The datagram for the node owning PEER-PUBLIC carrying PLAIN: its short id, then the encrypted message."
  (%cat (adnl-short-id peer-public) (adnl-udp-encrypt peer-public plain ephemeral)))

(defun adnl-udp-open-datagram (keypair datagram)
  "(VALUES PLAIN) of a DATAGRAM addressed to the owner of KEYPAIR; signals when it is addressed to another id."
  (when (< (length datagram) 96)
    (adnl-protocol-error "ADNL UDP datagram too short (~D octets)" (length datagram)))
  (unless (equalp (subseq datagram 0 32) (adnl-short-id (keypair-public keypair)))
    (adnl-protocol-error "ADNL UDP datagram for another id"))
  (adnl-udp-decrypt keypair (subseq datagram 32)))

;;; --- channels: AES with a shared secret -------------------------------------------------------------------------------------------------

(defun adnl-udp-aes-encrypt (secret plain)
  "digest (32) || AES-CTR(PLAIN) with the 32-octet channel SECRET (keys/encryptor.cpp, EncryptorAES)."
  (let* ((plain (as-octets plain))
         (digest (sha256 plain)))
    (multiple-value-bind (key iv) (adnl-udp-key-iv secret digest)
      (%cat digest (adnl-cipher-apply (adnl-make-cipher key iv) plain)))))

(defun adnl-udp-aes-decrypt (secret message)
  "The plain text of a message ADNL-UDP-AES-ENCRYPT made with SECRET; signals on a bad digest."
  (when (< (length message) 32) (adnl-protocol-error "ADNL UDP channel message too short"))
  (let ((digest (subseq message 0 32)))
    (multiple-value-bind (key iv) (adnl-udp-key-iv secret digest)
      (let ((plain (adnl-cipher-apply (adnl-make-cipher key iv) (subseq message 32))))
        (unless (equalp (sha256 plain) digest) (adnl-protocol-error "ADNL UDP channel: sha256 mismatch"))
        plain))))

(defun adnl-udp-channel-id (aes-key)
  "The id of a channel direction: sha256 of the boxed pub.aes of its key."
  (sha256 (tl-encode (tl-make "pub.aes" :key (coerce aes-key 'tl-octets)))))

(defun adnl-udp-id< (a b)
  "Octet-wise lexicographic order of two 32-octet short ids (the node's AdnlNodeIdShort <)."
  (loop for x across a for y across b
        do (cond ((< x y) (return t)) ((> x y) (return nil)))
        finally (return nil)))

(defun adnl-udp-channel-keys (local-id peer-id my-channel-seed peer-channel-public)
  "(VALUES IN-KEY OUT-KEY) of a channel between LOCAL-ID and PEER-ID, as adnl-channel.cpp derives them."
  (let* ((shared (adnl-shared-secret my-channel-seed peer-channel-public))
         (rev (reverse shared)))
    (cond ((adnl-udp-id< local-id peer-id) (values shared rev))
          ((adnl-udp-id< peer-id local-id) (values rev shared))
          (t (values shared shared)))))

(defun adnl-udp-make-channel-packet (messages &key seqno confirm-seqno)
  "A packet for a channel: messages, seqno and confirm_seqno only (unsigned, no source)."
  (let ((flags (logior (if (= 1 (length messages)) +adnl-udp-flag-message+ +adnl-udp-flag-messages+)
                       (if seqno +adnl-udp-flag-seqno+ 0)
                       (if confirm-seqno +adnl-udp-flag-confirm+ 0))))
    (tl-encode (tl-make "adnl.packetContents"
                        :rand1 (%adnl-udp-random-pad) :flags flags
                        :message (and (= 1 (length messages)) (first messages))
                        :messages (and (/= 1 (length messages)) (coerce messages 'vector))
                        :seqno seqno :confirm-seqno confirm-seqno :rand2 (%adnl-udp-random-pad)))))

;;; --- the signed packet ----------------------------------------------------------------------------------------------------------------

(defconstant +adnl-udp-flag-from+ #x1)
(defconstant +adnl-udp-flag-message+ #x4)
(defconstant +adnl-udp-flag-messages+ #x8)
(defconstant +adnl-udp-flag-address+ #x10)
(defconstant +adnl-udp-flag-seqno+ #x40)
(defconstant +adnl-udp-flag-confirm+ #x80)
(defconstant +adnl-udp-flag-reinit+ #x400)
(defconstant +adnl-udp-flag-signature+ #x800)

(defun %adnl-udp-random-pad ()
  (ironclad:random-data (if (logbitp 0 (aref (ironclad:random-data 1) 0)) 7 15)))

(defun adnl-udp-address-list (&key (version (unix-now)) (reinit-date (unix-now)))
  "An adnl.addressList with NO address: the peer answers to the address the datagram came from."
  (tl-make "adnl.addressList" :addrs '() :version version :reinit-date reinit-date :priority 0 :expire-at 0))

(defun adnl-udp-packet-to-sign (packet)
  "The octets a packet's signature covers: the packet without the signature and without its flag."
  (tl-encode (tl-make "adnl.packetContents"
                      :rand1 (tl-get packet :rand1)
                      :flags (logandc2 (tl-get packet :flags) +adnl-udp-flag-signature+)
                      :from (tl-get packet :from) :from-short (tl-get packet :from-short)
                      :message (tl-get packet :message) :messages (tl-get packet :messages)
                      :address (tl-get packet :address) :priority-address (tl-get packet :priority-address)
                      :seqno (tl-get packet :seqno) :confirm-seqno (tl-get packet :confirm-seqno)
                      :recv-addr-list-version (tl-get packet :recv-addr-list-version)
                      :recv-priority-addr-list-version (tl-get packet :recv-priority-addr-list-version)
                      :reinit-date (tl-get packet :reinit-date) :dst-reinit-date (tl-get packet :dst-reinit-date)
                      :signature nil :rand2 (tl-get packet :rand2))))

(defun adnl-udp-make-packet (keypair messages &key seqno confirm-seqno reinit-date dst-reinit-date address)
  "A signed adnl.packetContents from KEYPAIR carrying MESSAGES (adnl.Message objects) as serialized octets, ready to be
encrypted: the sender's key is always included, the rest only where given."
  (let* ((flags (logior +adnl-udp-flag-from+
                        (if (= 1 (length messages)) +adnl-udp-flag-message+ +adnl-udp-flag-messages+)
                        (if address +adnl-udp-flag-address+ 0)
                        (if seqno +adnl-udp-flag-seqno+ 0)
                        (if confirm-seqno +adnl-udp-flag-confirm+ 0)
                        (if reinit-date +adnl-udp-flag-reinit+ 0)))
         (packet (tl-make "adnl.packetContents"
                          :rand1 (%adnl-udp-random-pad) :flags flags
                          :from (tl-make "pub.ed25519" :key (coerce (keypair-public keypair) 'tl-octets))
                          :message (and (= 1 (length messages)) (first messages))
                          :messages (and (/= 1 (length messages)) (coerce messages 'vector))
                          :address address :seqno seqno :confirm-seqno confirm-seqno
                          :reinit-date reinit-date :dst-reinit-date (and reinit-date (or dst-reinit-date 0))
                          :rand2 (%adnl-udp-random-pad)))
         (signature (sign-octets keypair (adnl-udp-packet-to-sign packet))))
    (tl-encode (tl-make "adnl.packetContents"
                        :rand1 (tl-get packet :rand1) :flags (logior flags +adnl-udp-flag-signature+)
                        :from (tl-get packet :from)
                        :message (tl-get packet :message) :messages (tl-get packet :messages)
                        :address address :seqno seqno :confirm-seqno confirm-seqno
                        :reinit-date reinit-date :dst-reinit-date (tl-get packet :dst-reinit-date)
                        :signature (coerce signature 'tl-octets) :rand2 (tl-get packet :rand2)))))

(defun adnl-udp-open-packet (plain)
  "(VALUES PACKET SENDER-PUBLIC) of the decrypted PLAIN octets: decoded, with the signature checked against the key the
packet names; signals for a packet without a key or a signature, or whose signature is wrong."
  (let ((packet (tl-decode plain)))
    (unless (tl-is packet "adnl.packetContents") (adnl-protocol-error "not an adnl.packetContents"))
    (let ((flags (tl-get packet :flags)))
      (unless (and (logtest flags +adnl-udp-flag-from+) (logtest flags +adnl-udp-flag-signature+))
        (adnl-protocol-error "ADNL packet without a source key or a signature"))
      (let ((public (coerce (tl-get (tl-get packet :from) :key) 'octets)))
        (unless (ignore-errors
                 (ironclad:verify-signature (ironclad:make-public-key :ed25519 :y public)
                                            (adnl-udp-packet-to-sign packet)
                                            (as-octets (tl-get packet :signature))))
          (adnl-protocol-error "ADNL packet: bad signature"))
        (values packet public)))))

(defun adnl-udp-packet-messages (packet)
  "The adnl.Message objects of PACKET, as a list."
  (let ((flags (tl-get packet :flags)))
    (cond ((logtest flags +adnl-udp-flag-message+) (list (tl-get packet :message)))
          ((logtest flags +adnl-udp-flag-messages+) (coerce (tl-get packet :messages) 'list))
          (t '()))))

;;; --- a node: one UDP socket, a receive thread, peers, channels, queries ----------------------------------------------------------

(defstruct (adnl-udp-peer (:copier nil))
  public short-id host port
  (out-seqno 0) (in-seqno 0) (seen (make-hash-table))
  (reinit-date 0)                       ; the peer's, as it told us
  ;; the channel
  channel-keypair (channel-date 0) peer-channel-public (peer-channel-date 0)
  in-id out-id in-key out-key channel-inited channel-ready
  ;; a big message being put together from parts
  huge-hash huge-buffer (huge-offset 0)
  ;; what we know of the peer
  (rtt nil)                             ; round trip, seconds, smoothed (EWMA 0.3), NIL before the first answer
  (failures 0) (answers 0))

(defstruct (adnl-udp (:constructor %make-adnl-udp) (:copier nil))
  keypair short-id socket port handler
  (peers (make-hash-table :test 'equalp))
  (channels (make-hash-table :test 'equalp)) ; in-id -> peer
  (pending (make-hash-table :test 'equalp))
  (lock (sb-thread:make-mutex :name "adnl-udp"))
  (start-time (unix-now))
  thread (running t)
  (dropped 0) (channel-packets 0))

(defstruct (adnl-udp-pending (:copier nil)) answer (semaphore (sb-thread:make-semaphore)) (sent-at 0) peer)

(defun %adnl-udp-peer (node public host port)
  "The peer record of PUBLIC, created on first sight; its address follows the newest datagram."
  (sb-thread:with-mutex ((adnl-udp-lock node))
    (let* ((id (adnl-short-id public))
           (peer (or (gethash id (adnl-udp-peers node))
                     (setf (gethash id (adnl-udp-peers node))
                           (make-adnl-udp-peer :public (copy-seq public) :short-id id)))))
      (when host (setf (adnl-udp-peer-host peer) host (adnl-udp-peer-port peer) port))
      peer)))

(defun %adnl-udp-channel-keypair (peer)
  "The channel key pair of PEER's side, made on first use (its date goes into createChannel)."
  (or (adnl-udp-peer-channel-keypair peer)
      (progn (setf (adnl-udp-peer-channel-keypair peer) (adnl-generate-keypair)
                   (adnl-udp-peer-channel-date peer) (unix-now))
             (adnl-udp-peer-channel-keypair peer))))

(defun %adnl-udp-create-channel (node peer public date)
  "create_channel of adnl-peer.cpp: take the peer's channel key PUBLIC (made at DATE) unless it is the one already used or an older one."
  (sb-thread:with-mutex ((adnl-udp-lock node))
    (unless (or (and (adnl-udp-peer-channel-inited peer) (equalp (adnl-udp-peer-peer-channel-public peer) public))
                (and (adnl-udp-peer-channel-inited peer) (<= date (adnl-udp-peer-peer-channel-date peer))))
      (when (adnl-udp-peer-channel-inited peer)
        (remhash (adnl-udp-peer-in-id peer) (adnl-udp-channels node))
        (setf (adnl-udp-peer-channel-inited peer) nil (adnl-udp-peer-channel-ready peer) nil))
      (let ((mine (%adnl-udp-channel-keypair peer)))
        (setf (adnl-udp-peer-peer-channel-public peer) (copy-seq public)
              (adnl-udp-peer-peer-channel-date peer) date)
        (multiple-value-bind (in out)
            (adnl-udp-channel-keys (adnl-udp-short-id node) (adnl-udp-peer-short-id peer) (keypair-secret mine) public)
          (setf (adnl-udp-peer-in-key peer) in (adnl-udp-peer-out-key peer) out
                (adnl-udp-peer-in-id peer) (adnl-udp-channel-id in) (adnl-udp-peer-out-id peer) (adnl-udp-channel-id out)
                (adnl-udp-peer-channel-inited peer) t)
          (setf (gethash (adnl-udp-peer-in-id peer) (adnl-udp-channels node)) peer))))))

(defun %adnl-udp-channel-message (peer)
  "The channel message the next packet to PEER carries: createChannel before there is a channel, confirmChannel until
it is ready, none after."
  (let ((mine (%adnl-udp-channel-keypair peer)))
    (cond ((not (adnl-udp-peer-channel-inited peer))
           (tl-make "adnl.message.createChannel" :key (coerce (keypair-public mine) 'tl-octets)
                                                 :date (adnl-udp-peer-channel-date peer)))
          ((not (adnl-udp-peer-channel-ready peer))
           (tl-make "adnl.message.confirmChannel" :key (coerce (keypair-public mine) 'tl-octets)
                                                  :peer-key (coerce (adnl-udp-peer-peer-channel-public peer) 'tl-octets)
                                                  :date (adnl-udp-peer-channel-date peer)))
          (t nil))))

(defun %adnl-udp-split-message (message)
  "MESSAGE as a list of messages that each fit a datagram: itself, or adnl.message.part pieces of its boxed serialization."
  (let ((octets (tl-encode message)))
    (cond ((<= (length octets) (+ +adnl-udp-part-size+ 128)) (list message))
          ((> (length octets) +adnl-udp-max-message+)
           (ton-error "ADNL message of ~D octets is bigger than the ~D the node accepts" (length octets) +adnl-udp-max-message+))
          (t (let ((hash (sha256 octets)) (size (length octets)))
               (loop for offset from 0 below size by +adnl-udp-part-size+
                     collect (tl-make "adnl.message.part" :hash (coerce hash 'tl-octets) :total-size size :offset offset
                                                          :data (coerce (subseq octets offset (min size (+ offset +adnl-udp-part-size+)))
                                                                        'tl-octets))))))))

(defun %adnl-udp-send-packet (node peer messages)
  "One datagram of MESSAGES to PEER: through the channel once it is ready, else a signed packet that also carries the channel message."
  (let* ((seqno (sb-thread:with-mutex ((adnl-udp-lock node)) (incf (adnl-udp-peer-out-seqno peer))))
         (confirm (adnl-udp-peer-in-seqno peer))
         (channel-message (%adnl-udp-channel-message peer))
         (messages (if channel-message (cons channel-message messages) messages))
         (datagram
           (if (adnl-udp-peer-channel-ready peer)
               (%cat (adnl-udp-peer-out-id peer)
                     (adnl-udp-aes-encrypt (adnl-udp-peer-out-key peer)
                                           (adnl-udp-make-channel-packet messages :seqno seqno :confirm-seqno confirm)))
               (adnl-udp-datagram
                (adnl-udp-peer-public peer)
                (adnl-udp-make-packet (adnl-udp-keypair node) messages
                                      :seqno seqno :confirm-seqno confirm
                                      :reinit-date (adnl-udp-start-time node)
                                      :dst-reinit-date (adnl-udp-peer-reinit-date peer)
                                      :address (adnl-udp-address-list :version (adnl-udp-start-time node)
                                                                      :reinit-date (adnl-udp-start-time node)))))))
    (when (> (length datagram) +adnl-udp-max-datagram+)
      (ton-error "ADNL UDP datagram of ~D octets does not fit the ~D of the network" (length datagram) +adnl-udp-max-datagram+))
    (sb-bsd-sockets:socket-send (adnl-udp-socket node) datagram nil
                                :address (list (adnl-udp-peer-host peer) (adnl-udp-peer-port peer)))))

(defun %adnl-udp-send-messages (node peer messages)
  "Send MESSAGES to PEER, a big one in parts, each piece in a datagram of its own."
  (dolist (message messages)
    (dolist (piece (%adnl-udp-split-message message))
      (%adnl-udp-send-packet node peer (list piece)))))

(defun %adnl-udp-accept (node packet peer)
  "The replay and ordering rules of a received PACKET from PEER; true when it is to be processed."
  (sb-thread:with-mutex ((adnl-udp-lock node))
    (let ((seqno (or (tl-get packet :seqno) 0))
          (reinit (or (tl-get packet :reinit-date) 0)))
      (cond ((> reinit (+ (unix-now) 60)) nil)                         ; a date from the future
            ((and (plusp reinit) (< reinit (adnl-udp-peer-reinit-date peer))) nil) ; an older incarnation
            ((and (plusp seqno) (gethash seqno (adnl-udp-peer-seen peer))) nil)    ; a replay
            (t (when (> reinit (adnl-udp-peer-reinit-date peer))
                 (setf (adnl-udp-peer-reinit-date peer) reinit
                       (adnl-udp-peer-in-seqno peer) 0)
                 (clrhash (adnl-udp-peer-seen peer)))
               (when (plusp seqno)
                 (setf (gethash seqno (adnl-udp-peer-seen peer)) t
                       (adnl-udp-peer-in-seqno peer) (max seqno (adnl-udp-peer-in-seqno peer))))
               t)))))

(defun %adnl-udp-part (node peer message)
  "The reassembly of adnl.message.part pieces, as process_message of adnl-peer.cpp: in order, the hash checked at the end."
  (let ((hash (as-octets (tl-get message :hash)))
        (size (tl-get message :total-size))
        (offset (tl-get message :offset))
        (data (as-octets (tl-get message :data)))
        (done nil))
    (sb-thread:with-mutex ((adnl-udp-lock node))
      (cond
        ((or (> size +adnl-udp-max-message+) (every #'zerop hash)) nil)
        (t
         (unless (equalp hash (adnl-udp-peer-huge-hash peer))
           (setf (adnl-udp-peer-huge-hash peer) nil (adnl-udp-peer-huge-buffer peer) nil (adnl-udp-peer-huge-offset peer) 0)
           (when (zerop offset)
             (setf (adnl-udp-peer-huge-hash peer) hash
                   (adnl-udp-peer-huge-buffer peer) (make-array size :element-type '(unsigned-byte 8)))))
         (let ((buffer (adnl-udp-peer-huge-buffer peer)))
           (when (and buffer (= size (length buffer)) (<= (+ offset (length data)) size)
                      (= offset (adnl-udp-peer-huge-offset peer)))
             (replace buffer data :start1 offset)
             (incf (adnl-udp-peer-huge-offset peer) (length data))
             (when (= (adnl-udp-peer-huge-offset peer) size)
               (setf done (and (equalp (sha256 buffer) hash) buffer))
               (setf (adnl-udp-peer-huge-hash peer) nil (adnl-udp-peer-huge-buffer peer) nil
                     (adnl-udp-peer-huge-offset peer) 0)))))))
    (when done
      (let ((inner (ignore-errors (tl-decode done))))
        (when inner (%adnl-udp-process node peer inner))))))

(defun %adnl-udp-process (node peer message)
  (cond
    ((tl-is message "adnl.message.query")
     (let ((handler (adnl-udp-handler node)))
       (when handler
         (let ((answer (ignore-errors (funcall handler (as-octets (tl-get message :query)) (adnl-udp-peer-public peer)))))
           (when answer
             (%adnl-udp-send-messages
              node peer
              (list (tl-make "adnl.message.answer" :query-id (tl-get message :query-id)
                                                   :answer (coerce answer 'tl-octets)))))))))
    ((tl-is message "adnl.message.answer")
     (let ((entry (sb-thread:with-mutex ((adnl-udp-lock node))
                    (gethash (as-octets (tl-get message :query-id)) (adnl-udp-pending node)))))
       (when entry
         (setf (adnl-udp-pending-answer entry) (as-octets (tl-get message :answer)))
         (sb-thread:signal-semaphore (adnl-udp-pending-semaphore entry)))))
    ((tl-is message "adnl.message.part") (%adnl-udp-part node peer message))
    ((tl-is message "adnl.message.createChannel")
     (%adnl-udp-create-channel node peer (as-octets (tl-get message :key)) (tl-get message :date)))
    ((tl-is message "adnl.message.confirmChannel")
     (when (equalp (as-octets (tl-get message :peer-key)) (keypair-public (%adnl-udp-channel-keypair peer)))
       (%adnl-udp-create-channel node peer (as-octets (tl-get message :key)) (tl-get message :date))
       (sb-thread:with-mutex ((adnl-udp-lock node))
         (when (and (adnl-udp-peer-channel-inited peer)
                    (equalp (adnl-udp-peer-peer-channel-public peer) (as-octets (tl-get message :key))))
           (setf (adnl-udp-peer-channel-ready peer) t)))))
    (t nil)))                           ; nop and reinit: nothing to do

(defun %adnl-udp-deliver (node packet peer)
  (if (%adnl-udp-accept node packet peer)
      (dolist (message (adnl-udp-packet-messages packet))
        (%adnl-udp-process node peer message))
      (incf (adnl-udp-dropped node))))

(defun %adnl-udp-handle-datagram (node datagram host port)
  (handler-case
      (let ((dst (subseq datagram 0 32)))
        (if (equalp dst (adnl-udp-short-id node))
            (multiple-value-bind (packet public) (adnl-udp-open-packet (adnl-udp-open-datagram (adnl-udp-keypair node) datagram))
              (%adnl-udp-deliver node packet (%adnl-udp-peer node public host port)))
            (let ((peer (sb-thread:with-mutex ((adnl-udp-lock node)) (gethash dst (adnl-udp-channels node)))))
              (if (null peer)
                  (incf (adnl-udp-dropped node))
                  (let ((packet (tl-decode (adnl-udp-aes-decrypt (adnl-udp-peer-in-key peer) (subseq datagram 32)))))
                    (unless (tl-is packet "adnl.packetContents") (adnl-protocol-error "not a packet"))
                    (incf (adnl-udp-channel-packets node))
                    (when (and host (adnl-udp-peer-host peer))
                      (setf (adnl-udp-peer-host peer) host (adnl-udp-peer-port peer) port))
                    (sb-thread:with-mutex ((adnl-udp-lock node))
                      (when (and (adnl-udp-peer-channel-inited peer) (not (adnl-udp-peer-channel-ready peer)))
                        (setf (adnl-udp-peer-channel-ready peer) t)))
                    (%adnl-udp-deliver node packet peer))))))
    (error () (incf (adnl-udp-dropped node)))))

(defun %adnl-udp-receive-loop (node)
  (let ((buffer (make-array 2048 :element-type '(unsigned-byte 8)))
        (socket (adnl-udp-socket node)))
    (loop while (adnl-udp-running node)
          do (when (sb-sys:wait-until-fd-usable (sb-bsd-sockets:socket-file-descriptor socket) :input 0.1)
               (handler-case
                   (multiple-value-bind (buf length host port) (sb-bsd-sockets:socket-receive socket buffer nil)
                     (when (and buf length (plusp length))
                       (%adnl-udp-handle-datagram node (subseq buf 0 length) host port)))
                 (error () nil))))))

(defun adnl-udp-start (&key (keypair (adnl-generate-keypair)) (host "127.0.0.1") (port 0) handler)
  "A node: a UDP socket bound to HOST:PORT (0 = any free port) and the thread reading it.  HANDLER, when given, answers
queries: (funcall HANDLER query-octets sender-public) returns the answer octets, or NIL to stay silent."
  (let ((socket (make-instance 'sb-bsd-sockets:inet-socket :type :datagram :protocol :udp)))
    (setf (sb-bsd-sockets:sockopt-reuse-address socket) t)
    (sb-bsd-sockets:socket-bind socket (sb-bsd-sockets:make-inet-address host) port)
    (let ((node (%make-adnl-udp :keypair keypair :short-id (adnl-short-id (keypair-public keypair))
                                :socket socket :handler handler
                                :port (nth-value 1 (sb-bsd-sockets:socket-name socket)))))
      (setf (adnl-udp-thread node)
            (sb-thread:make-thread (lambda () (%adnl-udp-receive-loop node)) :name "adnl-udp-receive"))
      node)))

(defun adnl-udp-stop (node)
  "Stop the receive thread and close the socket."
  (setf (adnl-udp-running node) nil)
  (when (adnl-udp-thread node) (ignore-errors (sb-thread:join-thread (adnl-udp-thread node) :default nil)))
  (ignore-errors (sb-bsd-sockets:socket-close (adnl-udp-socket node)))
  t)

(defun adnl-udp-query (node host port peer-public query &key (timeout 5) (resend 1))
  "Send the adnl.message.query QUERY (octets, up to about 8 KB) to the node at HOST:PORT owning PEER-PUBLIC and wait for its
answer (octets).  The query is sent again every RESEND seconds until TIMEOUT (UDP loses datagrams); the first answer wins.  The
peer's round trip time (smoothed) and failure count are kept.  Signals ADNL-UDP-TIMEOUT when none comes."
  (let* ((peer (%adnl-udp-peer node peer-public (sb-bsd-sockets:make-inet-address host) port))
         (query-id (ironclad:random-data 32))
         (entry (make-adnl-udp-pending :peer peer))
         (message (tl-make "adnl.message.query" :query-id (coerce query-id 'tl-octets) :query (coerce query 'tl-octets)))
         (deadline (+ (get-internal-real-time) (* timeout internal-time-units-per-second))))
    (sb-thread:with-mutex ((adnl-udp-lock node))
      (setf (gethash query-id (adnl-udp-pending node)) entry))
    (unwind-protect
         (loop
           (setf (adnl-udp-pending-sent-at entry) (get-internal-real-time))
           (%adnl-udp-send-messages node peer (list message))
           (let ((left (/ (- deadline (get-internal-real-time)) internal-time-units-per-second)))
             (when (sb-thread:wait-on-semaphore (adnl-udp-pending-semaphore entry) :timeout (max 0.001 (min resend left)))
               (let ((rtt (/ (- (get-internal-real-time) (adnl-udp-pending-sent-at entry)) internal-time-units-per-second)))
                 (sb-thread:with-mutex ((adnl-udp-lock node))
                   (setf (adnl-udp-peer-rtt peer) (if (adnl-udp-peer-rtt peer)
                                                      (+ (* 0.7 (adnl-udp-peer-rtt peer)) (* 0.3 rtt))
                                                      rtt))
                   (incf (adnl-udp-peer-answers peer))))
               (return (adnl-udp-pending-answer entry)))
             (when (<= (- deadline (get-internal-real-time)) 0)
               (sb-thread:with-mutex ((adnl-udp-lock node)) (incf (adnl-udp-peer-failures peer)))
               (error 'adnl-udp-timeout :format-control "ADNL UDP query to ~A:~D: no answer in ~As"
                                        :format-arguments (list host port timeout)))))
      (sb-thread:with-mutex ((adnl-udp-lock node))
        (remhash query-id (adnl-udp-pending node))))))

(defun adnl-udp-peer-of (node public)
  "The peer record of the key PUBLIC, or NIL when the node has never met it."
  (sb-thread:with-mutex ((adnl-udp-lock node))
    (gethash (adnl-short-id public) (adnl-udp-peers node))))
