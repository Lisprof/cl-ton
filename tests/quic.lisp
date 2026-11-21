;;;; tests/quic.lisp -- QUIC packet protection (src/quic.lisp) against the sample packets of RFC 9001
;;;; Appendix A: key derivation, the client and server Initial packets byte for byte, and the Retry
;;;; integrity tag.  The vectors are the RFC's own, so a green run here means the packet layer speaks
;;;; the same QUIC as every other implementation, the node's ngtcp2 stack included.

(in-package :cl-ton/test)

(defun %quic-hex (string)
  (let ((out (make-array (/ (length string) 2) :element-type '(unsigned-byte 8))))
    (dotimes (i (length out) out)
      (setf (aref out i) (parse-integer string :start (* 2 i) :end (+ (* 2 i) 2) :radix 16)))))

(defun %quic-cat (&rest strings) (apply #'concatenate 'string strings))

(defparameter *quic-rfc-client-payload*
  (%quic-hex (%quic-cat
    "060040f1010000ed0303ebf8fa56f12939b9584a3896472ec40bb863cfd3e86804fe3a47f06a2b69484c000004130113"
    "02010000c000000010000e00000b6578616d706c652e636f6dff01000100000a00080006001d00170018001000070005"
    "04616c706e000500050100000000003300260024001d00209370b2c9caa47fbabaf4559fedba753de171fa71f50f1ce1"
    "5d43e994ec74d748002b0003020304000d0010000e0403050306030203080408050806002d00020101001c0002400100"
    "3900320408ffffffffffffffff05048000ffff07048000ffff0801100104800075300901100f088394c8f03e51570806"
    "048000ffff"))
  "RFC 9001 A.2: the CRYPTO frame of the client Initial, before padding.")

(defparameter *quic-rfc-client-packet*
  (%quic-hex (%quic-cat
    "c000000001088394c8f03e5157080000449e7b9aec34d1b1c98dd7689fb8ec11d242b123dc9bd8bab936b47d92ec356c"
    "0bab7df5976d27cd449f63300099f3991c260ec4c60d17b31f8429157bb35a1282a643a8d2262cad67500cadb8e7378c"
    "8eb7539ec4d4905fed1bee1fc8aafba17c750e2c7ace01e6005f80fcb7df621230c83711b39343fa028cea7f7fb5ff89"
    "eac2308249a02252155e2347b63d58c5457afd84d05dfffdb20392844ae812154682e9cf012f9021a6f0be17ddd0c208"
    "4dce25ff9b06cde535d0f920a2db1bf362c23e596d11a4f5a6cf3948838a3aec4e15daf8500a6ef69ec4e3feb6b1d98e"
    "610ac8b7ec3faf6ad760b7bad1db4ba3485e8a94dc250ae3fdb41ed15fb6a8e5eba0fc3dd60bc8e30c5c4287e53805db"
    "059ae0648db2f64264ed5e39be2e20d82df566da8dd5998ccabdae053060ae6c7b4378e846d29f37ed7b4ea9ec5d82e7"
    "961b7f25a9323851f681d582363aa5f89937f5a67258bf63ad6f1a0b1d96dbd4faddfcefc5266ba6611722395c906556"
    "be52afe3f565636ad1b17d508b73d8743eeb524be22b3dcbc2c7468d54119c7468449a13d8e3b95811a198f3491de3e7"
    "fe942b330407abf82a4ed7c1b311663ac69890f4157015853d91e923037c227a33cdd5ec281ca3f79c44546b9d90ca00"
    "f064c99e3dd97911d39fe9c5d0b23a229a234cb36186c4819e8b9c5927726632291d6a418211cc2962e20fe47feb3edf"
    "330f2c603a9d48c0fcb5699dbfe5896425c5bac4aee82e57a85aaf4e2513e4f05796b07ba2ee47d80506f8d2c25e50fd"
    "14de71e6c418559302f939b0e1abd576f279c4b2e0feb85c1f28ff18f58891ffef132eef2fa09346aee33c28eb130ff2"
    "8f5b766953334113211996d20011a198e3fc433f9f2541010ae17c1bf202580f6047472fb36857fe843b19f5984009dd"
    "c324044e847a4f4a0ab34f719595de37252d6235365e9b84392b061085349d73203a4a13e96f5432ec0fd4a1ee65accd"
    "d5e3904df54c1da510b0ff20dcc0c77fcb2c0e0eb605cb0504db87632cf3d8b4dae6e705769d1de354270123cb11450e"
    "fc60ac47683d7b8d0f811365565fd98c4c8eb936bcab8d069fc33bd801b03adea2e1fbc5aa463d08ca19896d2bf59a07"
    "1b851e6c239052172f296bfb5e72404790a2181014f3b94a4e97d117b438130368cc39dbb2d198065ae3986547926cd2"
    "162f40a29f0c3c8745c0f50fba3852e566d44575c29d39a03f0cda721984b6f440591f355e12d439ff150aab7613499d"
    "bd49adabc8676eef023b15b65bfc5ca06948109f23f350db82123535eb8a7433bdabcb909271a6ecbcb58b936a88cd4e"
    "8f2e6ff5800175f113253d8fa9ca8885c2f552e657dc603f252e1a8e308f76f0be79e2fb8f5d5fbbe2e30ecadd220723"
    "c8c0aea8078cdfcb3868263ff8f0940054da48781893a7e49ad5aff4af300cd804a6b6279ab3ff3afb64491c85194aab"
    "760d58a606654f9f4400e8b38591356fbf6425aca26dc85244259ff2b19c41b9f96f3ca9ec1dde434da7d2d392b905dd"
    "f3d1f9af93d1af5950bd493f5aa731b4056df31bd267b6b90a079831aaf579be0a39013137aac6d404f518cfd4684064"
    "7e78bfe706ca4cf5e9c5453e9f7cfd2b8b4c8d169a44e55c88d4a9a7f9474241e221af44860018ab0856972e194cd934"))
  "RFC 9001 A.2: the client Initial packet, protected.")

(defparameter *quic-rfc-server-payload*
  (%quic-hex (%quic-cat
    "02000000000600405a020000560303eefce7f7b37ba1d1632e96677825ddf73988cfc79825df566dc5430b9a045a1200"
    "130100002e00330024001d00209d3c940d89690b84d08a60993c144eca684d1081287c834d5311bcf32bb9da1a002b00"
    "020304"))
  "RFC 9001 A.3: the payload of the server Initial (ACK + CRYPTO frames).")

(defparameter *quic-rfc-server-packet*
  (%quic-hex (%quic-cat
    "cf000000010008f067a5502a4262b5004075c0d95a482cd0991cd25b0aac406a5816b6394100f37a1c69797554780bb3"
    "8cc5a99f5ede4cf73c3ec2493a1839b3dbcba3f6ea46c5b7684df3548e7ddeb9c3bf9c73cc3f3bded74b562bfb19fb84"
    "022f8ef4cdd93795d77d06edbb7aaf2f58891850abbdca3d20398c276456cbc42158407dd074ee"))
  "RFC 9001 A.3: the server Initial packet, protected.")

(defun test-quic ()
  (format t "~&QUIC packet protection (RFC 9001 Appendix A):~%")
  ;; variable-length integers: the examples of RFC 9000 section 16
  (dolist (pair '((37 . "25") (15293 . "7bbd") (494878333 . "9d7f3e7d")
                  (151288809941952652 . "c2197c5eff14e88c")))
    (check (format nil "quic varint ~D encodes" (car pair))
           (equalp (cl-ton::quic-encode-varint (car pair)) (%quic-hex (cdr pair))))
    (check (format nil "quic varint ~D decodes" (car pair))
           (= (cl-ton::quic-decode-varint (%quic-hex (cdr pair))) (car pair))))
  ;; packet numbers: RFC 9000 Appendix A examples
  (check "quic packet number decode"
         (= (cl-ton::quic-decode-packet-number #x9b32 2 #xa82f30ea) #xa82f9b32))
  (check "quic packet number encode"
         (multiple-value-bind (truncated count)
             (cl-ton::quic-encode-packet-number #xa82f9b32 #xa82f30ea)
           (and (= truncated #x9b32) (= count 2))))
  ;; Initial keys for the RFC's client DCID 8394c8f03e515708
  (let* ((dcid (%quic-hex "8394c8f03e515708"))
         (client (cl-ton::quic-initial-keys dcid :client))
         (server (cl-ton::quic-initial-keys dcid :server)))
    (check "quic client initial secret"
           (equalp (cl-ton::quic-keys-secret client)
                   (%quic-hex "c00cf151ca5be075ed0ebfb5c80323c42d6b7db67881289af4008f1f6c357aea")))
    (check "quic client initial key"
           (equalp (cl-ton::quic-keys-key client) (%quic-hex "1f369613dd76d5467730efcbe3b1a22d")))
    (check "quic client initial iv"
           (equalp (cl-ton::quic-keys-iv client) (%quic-hex "fa044b2f42a3fd3b46fb255c")))
    (check "quic client initial hp"
           (equalp (cl-ton::quic-keys-hp client) (%quic-hex "9f50449e04a0e810283a1e9933adedd2")))
    (check "quic server initial secret"
           (equalp (cl-ton::quic-keys-secret server)
                   (%quic-hex "3c199828fd139efd216c155ad844cc81fb82fa8d7446fa7d78be803acdda951b")))
    (check "quic server initial key"
           (equalp (cl-ton::quic-keys-key server) (%quic-hex "cf3a5331653c364c88f0f379b6067e37")))
    (check "quic server initial iv"
           (equalp (cl-ton::quic-keys-iv server) (%quic-hex "0ac1493ca1905853b0bba03e")))
    (check "quic server initial hp"
           (equalp (cl-ton::quic-keys-hp server) (%quic-hex "c206b8d9b9f0f37644430b490eeaa314")))
    ;; the client Initial, protected byte for byte as in the RFC
    (let* ((payload (make-array 1162 :element-type '(unsigned-byte 8) :initial-element 0))
           (_ (replace payload *quic-rfc-client-payload*))
           (header (cl-ton::quic-build-initial-header dcid #() #() (+ 4 1162 16) 4))
           (packet (cl-ton::quic-protect-packet client header 2 4 payload)))
      (declare (ignore _))
      (check "quic client initial header"
             (equalp header (%quic-hex "c300000001088394c8f03e5157080000449e")))
      (check "quic client initial packet (RFC 9001 A.2)"
             (equalp packet *quic-rfc-client-packet*))
      (check "quic client initial round trip"
             (multiple-value-bind (pn frames type)
                 (cl-ton::quic-unprotect-packet client packet)
               (and (= pn 2) (eq type :initial) (equalp frames payload)))))
    ;; the server Initial, opened with the server keys
    (check "quic server initial packet (RFC 9001 A.3)"
           (multiple-value-bind (pn frames type)
               (cl-ton::quic-unprotect-packet server *quic-rfc-server-packet*)
             (and (= pn 1) (eq type :initial) (equalp frames *quic-rfc-server-payload*)))))
  ;; the Retry integrity tag (RFC 9001 A.4)
  (let* ((retry (%quic-hex "ff000000010008f067a5502a4262b5746f6b656e04a265ba2eff4d829058fb3f0f2496ba"))
         (body (subseq retry 0 (- (length retry) 16)))
         (tag (subseq retry (- (length retry) 16))))
    (check "quic retry integrity tag (RFC 9001 A.4)"
           (equalp (cl-ton::quic-retry-integrity-tag body (%quic-hex "8394c8f03e515708")) tag))))

;;; --- the TLS 1.3 handshake: RFC 8448 section 3 key schedule, and a simulated TON server flight ---

(defparameter *quic-rfc8448-client-hello*
  (%quic-hex (%quic-cat

    "010000c00303cb34ecb1e78163ba1c38c6dacb196a6dffa21a8d9912ec18a2ef6283024dece700000613011303130201"
    "0000910000000b0009000006736572766572ff01000100000a00140012001d0017001800190100010101020103010400"
    "230000003300260024001d002099381de560e4bd43d23d8e435a7dbafeb3c06e51c13cae4d5413691e529aaf2c002b00"
    "03020304000d0020001e040305030603020308040805080604010501060102010402050206020202002d00020101001c"
    "00024001")))

(defparameter *quic-rfc8448-server-hello*
  (%quic-hex (%quic-cat

    "020000560303a6af06a4121860dc5e6e60249cd34c95930c8ac5cb1434dac155772ed3e2692800130100002e00330024"
    "001d0020c9828876112095fe66762bdbf7c672e156d6cc253b833df1dd69b1b04e751f0f002b00020304")))

(defun %quic-tls-hash (&rest messages)
  (cl-ton::tls-sha256 (cl-ton::concat-octets messages)))

(defun %quic-tls-basepoint ()
  (cl-ton::concat-octets (list (cl-ton::quic-octets 9)
                               (make-array 31 :element-type '(unsigned-byte 8) :initial-element 0))))

(defun %quic-tls-simulate (cert-request &key expected-id)
  "Run a whole handshake against a simulated TON server (raw-key certificate, ALPN \"ton\").
Returns (VALUES peer-ok params-ok flight) with FLIGHT the client's answering messages,
or signals on any failure."
  (let* ((client-seed (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x11))
         (server-seed (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x22))
         (server-keypair (cl-ton::seed->keypair server-seed))
         (server-public (cl-ton::keypair-public server-keypair))
         (dcid (%quic-hex "0102030405060708"))
         (client-scid (%quic-hex "a1a2a3a4a5a6a7a8"))
         (server-scid (%quic-hex "b1b2b3b4b5b6b7b8"))
         (peer-id (cl-ton::adnl-short-id server-public))
         (hex (cl-ton::octets->hex peer-id))
         (sni (concatenate 'string (subseq hex 0 32) "." (subseq hex 32) ".adnl"))
         (client (cl-ton::make-quic-tls :sni sni :expected-peer-id (or expected-id peer-id)
                                        :dcid dcid :scid client-scid :identity-seed client-seed))
         (ch (cl-ton::quic-tls-client-hello client))
         ;; the server side
         (server-xpriv (%quic-hex "b1580eeadf6dd589b8ef4f2d5652578cc810e9980191ec8d058308cea216a21e"))
         (server-xpub (cl-ton::x25519 server-xpriv (%quic-tls-basepoint)))
         (ecdhe (cl-ton::x25519 server-xpriv (cl-ton::qtls-x25519-public client)))
         (sh (cl-ton::tls-message
              2 (let ((exts (cl-ton::concat-octets
                             (list (cl-ton::tls-extension 43 (cl-ton::tls-u16 #x0304))
                                   (cl-ton::tls-extension 51 (cl-ton::concat-octets
                                                              (list (cl-ton::tls-u16 29)
                                                                    (cl-ton::tls-u16 (length server-xpub)) server-xpub)))))))
                  (cl-ton::concat-octets
                   (list (cl-ton::tls-u16 #x0303) (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x5a)
                         (cl-ton::quic-octets 0) (cl-ton::tls-u16 #x1301) (cl-ton::quic-octets 0)
                         (cl-ton::tls-u16 (length exts)) exts)))))
         (hs (cl-ton::tls-handshake-secret ecdhe))
         (hash-ch-sh (%quic-tls-hash ch sh))
         (c-hs (cl-ton::tls-derive-secret hs "c hs traffic" hash-ch-sh))
         (s-hs (cl-ton::tls-derive-secret hs "s hs traffic" hash-ch-sh))
         (ee (cl-ton::tls-message
              8 (let ((exts (cl-ton::concat-octets
                             (list (cl-ton::tls-extension 16 (cl-ton::concat-octets
                                                              (list (cl-ton::tls-u16 4) (cl-ton::quic-octets 3)
                                                                    (cl-ton::quic-ascii "ton"))))
                                   (cl-ton::tls-extension 20 (cl-ton::quic-octets 2))
                                   (cl-ton::tls-extension 57 (cl-ton::quic-encode-transport-parameters
                                                              (list (cons 0 dcid) (cons 15 server-scid)
                                                                    (cons 4 1048576) (cons 5 65536)
                                                                    (cons 6 65536) (cons 8 4))))))))
                  (cl-ton::concat-octets (list (cl-ton::tls-u16 (length exts)) exts)))))
         (cr (when cert-request
               (cl-ton::tls-message
                13 (cl-ton::concat-octets
                    (list (cl-ton::quic-octets 0)
                          (cl-ton::tls-u16 6)
                          (cl-ton::tls-extension 13 (cl-ton::concat-octets
                                                     (list (cl-ton::tls-u16 2) (cl-ton::tls-u16 #x0807)))))))))
         (spki (cl-ton::ed25519-spki server-public))
         (cert (cl-ton::tls-message
                11 (cl-ton::concat-octets
                    (list (cl-ton::quic-octets 0)
                          (cl-ton::tls-u24 (+ 3 (length spki) 2))
                          (cl-ton::tls-u24 (length spki)) spki (cl-ton::tls-u16 0)))))
         (before-cv (if cert-request (list ch sh ee cr cert) (list ch sh ee cert)))
         (cv (cl-ton::tls-message
              15 (let* ((content (cl-ton::concat-octets
                                  (list (make-array 64 :element-type '(unsigned-byte 8) :initial-element #x20)
                                        (cl-ton::quic-ascii "TLS 1.3, server CertificateVerify")
                                        (cl-ton::quic-octets 0)
                                        (apply #'%quic-tls-hash before-cv))))
                        (sig (ironclad:sign-message (ironclad:make-private-key :ed25519 :x server-seed) content)))
                   (cl-ton::concat-octets (list (cl-ton::tls-u16 #x0807)
                                                (cl-ton::tls-u16 (length sig)) sig)))))
         (sfin (cl-ton::tls-message
                20 (cl-ton::tls-verify-data s-hs (apply #'%quic-tls-hash (append before-cv (list cv))))))
         (flight-msgs (append (list ee) (when cert-request (list cr)) (list cert cv sfin))))
    ;; the client side
    (multiple-value-bind (c-hs-keys s-hs-keys) (cl-ton::quic-tls-process-server-hello client sh)
      (declare (ignore c-hs-keys s-hs-keys))
      (multiple-value-bind (flight c-ap s-ap) (cl-ton::quic-tls-process-flight client flight-msgs)
        (declare (ignore c-ap s-ap))
        (values (equalp (cl-ton::qtls-peer-public client) server-public)
                (= (cl-ton::quic-tp-integer (cl-ton::qtls-server-parameters client) 4) 1048576)
                flight
                (append before-cv (list cv sfin))
                c-hs
                client-seed)))))

(defun test-quic-tls ()
  (format t "~&QUIC TLS 1.3 handshake (RFC 8448 key schedule + simulated server):~%")
  ;; the key schedule of RFC 8448 section 3, step by step
  (let* ((early (cl-ton::tls-early-secret))
         (ecdhe (%quic-hex "8bd4054fb55b9d63fdfbacf9f04b9f0d35e6d63f537563efd46272900f89492d"))
         (hs (cl-ton::tls-handshake-secret ecdhe))
         (hash-ch-sh (%quic-hex "860c06edc07858ee8e78f0e7428c58edd6b43f2ca3e6e95f02ed063cf0e1cad8"))
         (c-hs (cl-ton::tls-derive-secret hs "c hs traffic" hash-ch-sh))
         (s-hs (cl-ton::tls-derive-secret hs "s hs traffic" hash-ch-sh))
         (master (cl-ton::tls-master-secret hs))
         (hash-ap (%quic-hex "9608102a0f1ccc6db6250b7b7e417b1a000eaada3daae4777a7686c9ff83df13")))
    (check "quic tls early secret (RFC 8448)"
           (equalp early (%quic-hex "33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a")))
    (check "quic tls handshake secret (RFC 8448)"
           (equalp hs (%quic-hex "1dc826e93606aa6fdc0aadc12f741b01046aa6b99f691ed221a9f0ca043fbeac")))
    (check "quic tls client handshake traffic secret (RFC 8448)"
           (equalp c-hs (%quic-hex "b3eddb126e067f35a780b3abf45e2d8f3b1a950738f52e9600746a0e27a55a21")))
    (check "quic tls server handshake traffic secret (RFC 8448)"
           (equalp s-hs (%quic-hex "b67b7d690cc16c4e75e54213cb2d37b4e9c912bcded9105d42befd59d391ad38")))
    (check "quic tls server handshake key/iv labels (RFC 8448)"
           (and (equalp (cl-ton::hkdf-expand-label s-hs "key" #() 16)
                        (%quic-hex "3fce516009c21727d0f2e4e86ee403bc"))
                (equalp (cl-ton::hkdf-expand-label s-hs "iv" #() 12)
                        (%quic-hex "5d313eb2671276ee13000b30"))))
    (check "quic tls finished key (RFC 8448)"
           (equalp (cl-ton::tls-finished-key s-hs)
                   (%quic-hex "008d3b66f816ea559f96b537e885c31fc068bf492c652f01f288a1d8cdc19fc8")))
    (check "quic tls master secret (RFC 8448)"
           (equalp master (%quic-hex "18df06843d13a08bf2a449844c5f8a478001bc4d4c627984d5a41da8d0402919")))
    (check "quic tls application traffic secrets (RFC 8448)"
           (and (equalp (cl-ton::tls-derive-secret master "c ap traffic" hash-ap)
                        (%quic-hex "9e40646ce79a7f9dc05af8889bce6552875afa0b06df0087f792ebb7c17504a5"))
                (equalp (cl-ton::tls-derive-secret master "s ap traffic" hash-ap)
                        (%quic-hex "a11af9f05531f856ad47116b45a950328204b4f44bfb6b3a4b4f1f3fcb631643"))))
    ;; the transcript hash over the RFC's own ClientHello and ServerHello
    (check "quic tls transcript hash (RFC 8448)"
           (equalp (%quic-tls-hash *quic-rfc8448-client-hello* *quic-rfc8448-server-hello*) hash-ch-sh)))
  ;; transport parameters and raw-key encodings round-trip
  (let* ((dcid (%quic-hex "0102030405060708"))
         (encoded (cl-ton::quic-encode-transport-parameters
                   (list (cons 0 dcid) (cons 1 30000) (cons 4 16777216) (cons 15 (%quic-hex "a1a2a3a4")))))
         (decoded (cl-ton::quic-decode-transport-parameters encoded)))
    (check "quic transport parameters round trip"
           (and (equalp (cdr (assoc 0 decoded)) dcid)
                (= (cl-ton::quic-tp-integer decoded 1) 30000)
                (= (cl-ton::quic-tp-integer decoded 4) 16777216))))
  (let ((key (cl-ton::keypair-public (cl-ton::seed->keypair (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7)))))
    (check "quic ed25519 SPKI round trip"
           (and (equalp (cl-ton::spki-ed25519 (cl-ton::ed25519-spki key)) key)
                (null (cl-ton::spki-ed25519 (cl-ton::quic-octets 1 2 3))))))
  ;; a full handshake against the simulated server, without and with a certificate request
  (dolist (cert-request '(nil t))
    (multiple-value-bind (peer-ok params-ok flight transcript c-hs client-seed)
        (%quic-tls-simulate cert-request)
      (check (format nil "quic tls simulated handshake (cert-request ~A): peer key" cert-request) peer-ok)
      (check (format nil "quic tls simulated handshake (cert-request ~A): server parameters" cert-request) params-ok)
      (check (format nil "quic tls simulated handshake (cert-request ~A): flight shape" cert-request)
             (= (length flight) (if cert-request 3 1)))
      (when cert-request
        (let* ((ccert (first flight))
               (ccv (second flight))
               (client-public (cl-ton::keypair-public (cl-ton::seed->keypair client-seed))))
          (check "quic tls client certificate carries our key"
                 (multiple-value-bind (entries n1) (cl-ton::tls-field ccert 5 3)
                   (declare (ignore n1))
                   (multiple-value-bind (spki n2) (cl-ton::tls-field entries 0 3)
                     (declare (ignore n2))
                     (equalp (cl-ton::spki-ed25519 spki) client-public))))
          (check "quic tls client CertificateVerify verifies"
                 (multiple-value-bind (sig next) (cl-ton::tls-field ccv 6 2)
                   (declare (ignore next))
                   (ironclad:verify-signature
                    (ironclad:make-public-key :ed25519 :y client-public)
                    (cl-ton::concat-octets
                     (list (make-array 64 :element-type '(unsigned-byte 8) :initial-element #x20)
                           (cl-ton::quic-ascii "TLS 1.3, client CertificateVerify")
                           (cl-ton::quic-octets 0)
                           (apply #'%quic-tls-hash (append transcript (list ccert)))))
                    sig)))))
      (check (format nil "quic tls simulated handshake (cert-request ~A): client Finished" cert-request)
             (let ((cfin (car (last flight)))
                   (msgs (append transcript (butlast flight))))
               (equalp (subseq cfin 4)
                       (cl-ton::tls-verify-data c-hs (apply #'%quic-tls-hash msgs)))))))
  ;; a server whose key does not hash to the expected ADNL id is refused
  (check "quic tls wrong peer id refused"
         (handler-case
             (progn (%quic-tls-simulate nil :expected-id (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x99))
                    nil)
           (error () t))))

;;; --- stage 3: a mock server on a simulated network -------------------------------------------------

(defvar *qnet* nil)
(defvar *qsrv* nil)

(defstruct (qnet (:conc-name qnet-))
  (lock (sb-thread:make-mutex :name "qnet"))
  (queue '())                           ; (deliver-at direction . datagram)
  (drop 0d0) (delay 0.005d0) (jitter 0.015d0)
  (sent 0) (dropped 0))

(defun %qnet-send (net direction datagram now)
  (sb-thread:with-mutex ((qnet-lock net))
    (incf (qnet-sent net))
    (if (< (random 1d0) (qnet-drop net))
        (incf (qnet-dropped net))
        (push (list (+ now (qnet-delay net) (random (qnet-jitter net))) direction datagram)
              (qnet-queue net)))))

(defstruct (qsrv (:conc-name qsrv-))
  net (scid (ironclad:random-data 8)) client-scid client-dcid
  keypair initial handshake app
  (transcript '())
  xpriv (sh-sent nil)
  hs-secret c-hs s-hs
  (streams (make-hash-table))
  (answer-fn (lambda (data) data))
  (established nil) (failed nil))

(defun %make-qsrv (net &key identity-seed answer-fn)
  (let ((srv (make-qsrv :net net
                        :keypair (cl-ton::seed->keypair identity-seed)
                        :xpriv (ironclad:random-data 32))))
    (when answer-fn (setf (qsrv-answer-fn srv) answer-fn))
    srv))

(defun %qsrv-stream (srv id)
  (or (gethash id (qsrv-streams srv))
      (setf (gethash id (qsrv-streams srv)) (cl-ton::make-quic-stream :id id))))

(defun %qsrv-xpub (srv)
  (cl-ton::x25519 (qsrv-xpriv srv)
                  (cl-ton::concat-octets (list (cl-ton::quic-octets 9)
                                               (make-array 31 :element-type '(unsigned-byte 8) :initial-element 0)))))

(defun %qsrv-on-client-hello (srv ch dcid)
  "Answer a ClientHello: ServerHello into the Initial space, the flight into the Handshake space."
  (let* ((at (+ 4 2 32))
         (sid-len (aref ch at))
         (sid (subseq ch (1+ at) (+ at 1 sid-len))))
    (setf at (+ at 1 sid-len))
    (incf at (+ 2 (cl-ton::tls-u16-at ch at)))
    (incf at (1+ (aref ch at)))
    (incf at 2)
    (let* ((extensions (cl-ton::tls-parse-extensions ch at (length ch)))
           (share (cdr (assoc 51 extensions)))
           (client-xpub (subseq share 6 (+ 6 (cl-ton::tls-u16-at share 4))))
           (ecdhe (cl-ton::x25519 (qsrv-xpriv srv) client-xpub))
           (hs (cl-ton::tls-handshake-secret ecdhe))
           (sh (cl-ton::tls-message
                2 (let ((exts (cl-ton::concat-octets
                               (list (cl-ton::tls-extension 43 (cl-ton::tls-u16 #x0304))
                                     (cl-ton::tls-extension 51 (cl-ton::concat-octets
                                                                (list (cl-ton::tls-u16 29)
                                                                      (cl-ton::tls-u16 (length (%qsrv-xpub srv)))
                                                                      (%qsrv-xpub srv))))))))
                    (cl-ton::concat-octets
                     (list (cl-ton::tls-u16 #x0303) (ironclad:random-data 32)
                           (cl-ton::quic-octets sid-len) sid
                           (cl-ton::tls-u16 #x1301) (cl-ton::quic-octets 0)
                           (cl-ton::tls-u16 (length exts)) exts))))))
      (setf (qsrv-hs-secret srv) hs)
      (push ch (qsrv-transcript srv))
      (push sh (qsrv-transcript srv))
      (cl-ton::%quic-append (cl-ton::qsp-crypto-send (qsrv-initial srv)) sh)
      (let* ((hash (%quic-tls-hash ch sh))
             (c-hs (cl-ton::tls-derive-secret hs "c hs traffic" hash))
             (s-hs (cl-ton::tls-derive-secret hs "s hs traffic" hash))
             (space (cl-ton::make-quic-space)))
        (setf (qsrv-c-hs srv) c-hs (qsrv-s-hs srv) s-hs
              (cl-ton::qsp-send-keys space) (cl-ton::quic-derive-keys s-hs)
              (cl-ton::qsp-recv-keys space) (cl-ton::quic-derive-keys c-hs)
              (qsrv-handshake srv) space)
        (let* ((tp (cl-ton::quic-encode-transport-parameters
                    (list (cons 0 dcid) (cons 1 0) (cons 3 65527) (cons 4 16777216)
                          (cons 5 1048576) (cons 6 1048576) (cons 7 1048576)
                          (cons 8 100) (cons 9 100) (cons 10 3) (cons 14 4)
                          (cons 15 (qsrv-scid srv)))))
               (ee (cl-ton::tls-message
                    8 (let ((exts (cl-ton::concat-octets
                                   (list (cl-ton::tls-extension 16 (cl-ton::concat-octets
                                                                    (list (cl-ton::tls-u16 4) (cl-ton::quic-octets 3)
                                                                          (cl-ton::quic-ascii "ton"))))
                                         (cl-ton::tls-extension 20 (cl-ton::quic-octets 2))
                                         (cl-ton::tls-extension 57 tp)))))
                        (cl-ton::concat-octets (list (cl-ton::tls-u16 (length exts)) exts)))))
               (spki (cl-ton::ed25519-spki (cl-ton::keypair-public (qsrv-keypair srv))))
               (cert (cl-ton::tls-message
                      11 (cl-ton::concat-octets
                          (list (cl-ton::quic-octets 0)
                                (cl-ton::tls-u24 (+ 4 (length spki)))
                                (cl-ton::tls-u24 (length spki)) spki (cl-ton::tls-u16 0))))))
          (push ee (qsrv-transcript srv))
          (push cert (qsrv-transcript srv))
          (let* ((content (cl-ton::concat-octets
                           (list (make-array 64 :element-type '(unsigned-byte 8) :initial-element #x20)
                                 (cl-ton::quic-ascii "TLS 1.3, server CertificateVerify")
                                 (cl-ton::quic-octets 0)
                                 (apply #'%quic-tls-hash (reverse (qsrv-transcript srv))))))
                 (sig (ironclad:sign-message
                       (ironclad:make-private-key :ed25519 :x
                                                  (cl-ton::keypair-secret (qsrv-keypair srv)))
                       content))
                 (cv (cl-ton::tls-message
                      15 (cl-ton::concat-octets (list (cl-ton::tls-u16 #x0807)
                                                      (cl-ton::tls-u16 (length sig)) sig)))))
            (push cv (qsrv-transcript srv))
            (let* ((fin (cl-ton::tls-message
                         20 (cl-ton::tls-verify-data
                             s-hs (apply #'%quic-tls-hash (reverse (qsrv-transcript srv))))))
                   (master (cl-ton::tls-master-secret hs))
                   (hash-fin (apply #'%quic-tls-hash (reverse (cons fin (qsrv-transcript srv)))))
                   (app (cl-ton::make-quic-space)))
              (push fin (qsrv-transcript srv))
              (setf (cl-ton::qsp-send-keys app)
                    (cl-ton::quic-derive-keys (cl-ton::tls-derive-secret master "s ap traffic" hash-fin))
                    (cl-ton::qsp-recv-keys app)
                    (cl-ton::quic-derive-keys (cl-ton::tls-derive-secret master "c ap traffic" hash-fin))
                    (qsrv-app srv) app)
              (dolist (m (list ee cert cv fin))
                (cl-ton::%quic-append (cl-ton::qsp-crypto-send space) m))
              (setf (qsrv-sh-sent srv) t))))))))

(defun %qsrv-crypto (srv space kind)
  (ecase kind
    (:initial
     (loop for m = (cl-ton::%quic-take-crypto-message space) while m do
       (when (and (= (aref m 0) 1) (not (qsrv-sh-sent srv)))
         (%qsrv-on-client-hello srv m (qsrv-client-dcid srv)))))
    (:handshake
     (loop for m = (cl-ton::%quic-take-crypto-message space) while m do
       (when (= (aref m 0) 20)
         (let ((expected (cl-ton::tls-verify-data
                          (qsrv-c-hs srv)
                          (apply #'%quic-tls-hash (reverse (qsrv-transcript srv))))))
           (when (equalp (subseq m 4) expected)
             (setf (qsrv-established srv) t))))))
    (:app nil)))

(defun %qsrv-answer (srv stream)
  (let* ((content (subseq (cl-ton::qr-buffer (cl-ton::qs-recv stream)) 0 (cl-ton::qs-recv-final-size stream)))
         (obj (ignore-errors (cl-ton::tl-decode content))))
    (when (and obj (cl-ton::tl-is obj "quic.query"))
      (setf (cl-ton::qs-send-data stream)
            (cl-ton::tl-encode (cl-ton::tl-make "quic.answer"
                                                :data (coerce (funcall (qsrv-answer-fn srv)
                                                                       (cl-ton::tl-get obj :data))
                                                              'cl-ton::tl-octets)))
            (cl-ton::qs-fin stream) t))))

(defun %qsrv-frames (srv space kind payload now)
  (let ((at 0) (end (length payload)) (eliciting nil))
    (labels ((varint ()
               (multiple-value-bind (v next) (cl-ton::quic-decode-varint payload :start at)
                 (setf at next) v))
             (take (n) (prog1 (subseq payload at (+ at n)) (incf at n))))
      (loop while (< at end) do
        (let ((type (aref payload at)))
          (incf at)
          (cond
            ((= type 0))
            ((= type 1) (setf eliciting t))
            ((or (= type 2) (= type 3))
             (multiple-value-bind (ranges delay next) (cl-ton::%qsp-parse-ack payload at)
               (declare (ignore delay))
               (setf at next)
               (when (= type 3) (varint) (varint) (varint))
               (cl-ton::%qsp-note-acked space ranges)))
            (t (setf eliciting t)
               (ecase type
                 (6 (let* ((offset (varint)) (len (varint)) (data (take len)))
                      (cl-ton::qr-feed (cl-ton::qsp-crypto-recv space) offset data)
                      (%qsrv-crypto srv space kind)))
                 ((8 9 10 11 12 13 14 15)
                  (let* ((id (varint))
                         (offset (if (logbitp 2 type) (varint) 0))
                         (len (if (logbitp 1 type) (varint) (- end at)))
                         (data (take len))
                         (fin (logbitp 0 type))
                         (stream (%qsrv-stream srv id)))
                    (cl-ton::qr-feed (cl-ton::qs-recv stream) offset data)
                    (when fin
                      (setf (cl-ton::qs-recv-fin stream) t
                            (cl-ton::qs-recv-final-size stream) (+ offset (length data))))
                    (when (and (cl-ton::qs-recv-fin stream) (cl-ton::qs-recv-final-size stream)
                               (>= (cl-ton::qr-end (cl-ton::qs-recv stream)) (cl-ton::qs-recv-final-size stream))
                               (not (cl-ton::qs-delivered stream)))
                      (setf (cl-ton::qs-delivered stream) t)
                      (%qsrv-answer srv stream))))
                 (28 (varint) (varint) (let ((rl (varint))) (take rl)) (setf (qsrv-failed srv) t))
                 (29 (varint) (let ((rl (varint))) (take rl)) (setf (qsrv-failed srv) t))))))))
    eliciting))

(defun %qsrv-collect (srv space kind budget)
  "The mock server's frame collection: ACK, CRYPTO resends and fresh data, STREAM data and FINs."
  (let ((parts '()) (used 0) (crypto '()) (streams '()) (fins '()))
    (labels ((emit (o) (push o parts) (incf used (length o)))
             (%room () (- budget used)))
      (when (and (cl-ton::qsp-ack-needed space) (cl-ton::qsp-received space))
        (let ((frame (cl-ton::%qsp-ack-frame space (cl-ton::rldp-clock) 3)))
          (when (and frame (<= (length frame) (%room)))
            (emit frame)
            (setf (cl-ton::qsp-ack-needed space) nil (cl-ton::qsp-ack-eliciting-since-ack space) 0))))
      (loop while (and (cl-ton::qsp-crypto-resend space) (> (%room) 8)) do
        (let* ((range (pop (cl-ton::qsp-crypto-resend space)))
               (take (min (cdr range) (- (%room) 8))))
          (when (> take 0)
            (emit (cl-ton::concat-octets (list (cl-ton::quic-octets 6) (cl-ton::quic-encode-varint (car range))
                                               (cl-ton::quic-encode-varint take)
                                               (subseq (cl-ton::qsp-crypto-send space) (car range) (+ (car range) take)))))
            (push (cons (car range) take) crypto)
            (when (< take (cdr range))
              (push (cons (+ (car range) take) (- (cdr range) take)) (cl-ton::qsp-crypto-resend space))))))
      (loop while (and (< (cl-ton::qsp-crypto-send-next space) (length (cl-ton::qsp-crypto-send space))) (> (%room) 8)) do
        (let* ((off (cl-ton::qsp-crypto-send-next space))
               (take (min (- (length (cl-ton::qsp-crypto-send space)) off) (- (%room) 8))))
          (when (> take 0)
            (emit (cl-ton::concat-octets (list (cl-ton::quic-octets 6) (cl-ton::quic-encode-varint off)
                                               (cl-ton::quic-encode-varint take)
                                               (subseq (cl-ton::qsp-crypto-send space) off (+ off take)))))
            (push (cons off take) crypto)
            (setf (cl-ton::qsp-crypto-send-next space) (+ off take)))))
      (when (eq kind :app)
        (dolist (id (sort (loop for id being the hash-keys of (qsrv-streams srv) collect id) #'<))
          (let ((stream (gethash id (qsrv-streams srv))))
            (loop while (and (cl-ton::qs-resend stream) (> (%room) 12)) do
              (let* ((range (pop (cl-ton::qs-resend stream)))
                     (take (min (cdr range) (- (%room) 12))))
                (when (> take 0)
                  (emit (cl-ton::%quic-stream-frame stream (car range) take nil))
                  (push (list id (car range) take) streams)
                  (when (< take (cdr range))
                    (push (cons (+ (car range) take) (- (cdr range) take)) (cl-ton::qs-resend stream))))))
            (loop while (and (cl-ton::qs-send-data stream)
                             (< (cl-ton::qs-send-next stream) (length (cl-ton::qs-send-data stream)))
                             (> (%room) 12)) do
              (let* ((off (cl-ton::qs-send-next stream))
                     (take (min (- (length (cl-ton::qs-send-data stream)) off) (- (%room) 12))))
                (emit (cl-ton::%quic-stream-frame stream off take nil))
                (push (list id off take) streams)
                (setf (cl-ton::qs-send-next stream) (+ off take))))
            (when (and (cl-ton::qs-fin stream) (not (cl-ton::qs-fin-sent stream))
                       (or (null (cl-ton::qs-send-data stream))
                           (>= (cl-ton::qs-send-next stream) (length (cl-ton::qs-send-data stream))))
                       (> (%room) 4))
              (emit (cl-ton::%quic-stream-frame stream (cl-ton::qs-send-next stream) 0 t))
              (push id fins)
              (setf (cl-ton::qs-fin-sent stream) t)))))
      (values (and parts (cl-ton::concat-octets (nreverse parts))) (nreverse crypto) (nreverse streams) (nreverse fins)))))

(defun %qsrv-flush (srv now)
  (dolist (slot '(initial handshake app))
    (let ((space (slot-value srv slot)) (kind (intern (symbol-name slot) :keyword)))
      (when space
        (loop
          (multiple-value-bind (frames crypto streams fins) (%qsrv-collect srv space kind 1150)
            (unless frames (return))
            (let* ((pn (cl-ton::qsp-next-pn space))
                   (header (ecase kind
                             (:initial (cl-ton::quic-build-initial-header (qsrv-client-scid srv) (qsrv-scid srv)
                                                                          (cl-ton::quic-octets) (+ 4 (length frames) 16) 4))
                             (:handshake (cl-ton::%quic-build-long-header 2 (qsrv-client-scid srv) (qsrv-scid srv)
                                                                          (+ 4 (length frames) 16) 4))
                             (:app (cl-ton::concat-octets (list (cl-ton::quic-octets #x43) (qsrv-client-scid srv))))))
                   (packet (cl-ton::quic-protect-packet (cl-ton::qsp-send-keys space) header pn 4 frames)))
              (setf (cl-ton::qsp-next-pn space) (1+ pn))
              (setf (gethash pn (cl-ton::qsp-sent space))
                    (cl-ton::make-qsent :time now :ack-eliciting t :crypto crypto :streams streams :fins fins))
              (%qnet-send (qsrv-net srv) :to-client packet now))))))))

(defun %qsrv-open-short (srv packet)
  (let* ((space (qsrv-app srv))
         (pn-at (1+ (length (qsrv-scid srv))))
         (sample-at (+ pn-at 4)))
    (when (and space (> (length packet) (+ pn-at 20)))
      (let* ((keys (cl-ton::qsp-recv-keys space))
             (mask (cl-ton::quic-header-mask keys (subseq packet sample-at (+ sample-at 16))))
             (first (logxor (aref packet 0) (logand (aref mask 0) #x1F)))
             (pn-length (1+ (ldb (byte 2 0) first)))
             (truncated 0))
        (dotimes (i pn-length)
          (setf truncated (logior (ash truncated 8)
                                  (logxor (aref packet (+ pn-at i)) (aref mask (1+ i))))))
        (let* ((pn (cl-ton::quic-decode-packet-number truncated pn-length (cl-ton::qsp-largest-received space)))
               (header (cl-ton::concat-octets (list (cl-ton::quic-octets first) (subseq packet 1 pn-at)
                                                    (cl-ton::uint->octets truncated pn-length))))
               (payload (cl-ton::quic-aead-open keys pn header (subseq packet (+ pn-at pn-length)))))
          (when payload (values pn payload)))))))

(defun %qsrv-receive (srv datagram now)
  (let ((at 0))
    (loop while (< at (length datagram)) do
      (let ((first (aref datagram at)))
        (cond
          ((logbitp 7 first)
           (multiple-value-bind (type dcid scid length-at packet-end) (cl-ton::quic-parse-long-header (subseq datagram at))
             (declare (ignore length-at))
             (when (or (null type) (null packet-end) (> (+ at packet-end) (length datagram)))
               (return))
             (let ((one (subseq datagram at (+ at packet-end))))
               ;; a real (ngtcp2) server discards an Initial carried in a datagram
               ;; smaller than 1200 octets (RFC 9000 14.1); the mock does the same,
               ;; so an under-padded client Initial fails here as it does on mainnet
               (when (and (eq type :initial) (< (length datagram) 1200))
                 (setf at (+ at packet-end))
                 (return))
               (when (eq type :initial)
                 (setf (qsrv-client-scid srv) scid)
                 (unless (qsrv-initial srv)
                   (setf (qsrv-client-dcid srv) dcid)
                   (let ((space (cl-ton::make-quic-space)))
                     (setf (cl-ton::qsp-send-keys space) (cl-ton::quic-initial-keys dcid :server)
                           (cl-ton::qsp-recv-keys space) (cl-ton::quic-initial-keys dcid :client)
                           (qsrv-initial srv) space))))
               (let ((space (ecase type (:initial (qsrv-initial srv)) (:handshake (qsrv-handshake srv)) (:zero-rtt nil))))
                 (when space
                   (multiple-value-bind (pn payload)
                       (cl-ton::quic-unprotect-packet (cl-ton::qsp-recv-keys space) one
                                                      :largest-received (cl-ton::qsp-largest-received space))
                     (when pn
                       (let ((eliciting (%qsrv-frames srv space type payload now)))
                         (cl-ton::%qsp-note-received space pn now eliciting)))))))
             (setf at (+ at packet-end))))
          (t
           (multiple-value-bind (pn payload) (%qsrv-open-short srv (subseq datagram at))
             (when pn
               (let ((eliciting (%qsrv-frames srv (qsrv-app srv) :app payload now)))
                 (cl-ton::%qsp-note-received (qsrv-app srv) pn now eliciting))))
           (setf at (length datagram)))))))
  (%qsrv-flush srv now))

(defun %qsrv-tick (srv now)
  (dolist (space (list (qsrv-initial srv) (qsrv-handshake srv) (qsrv-app srv)))
    (when space
      (let ((lost '()))
        (maphash (lambda (pn rec)
                   (when (and (cl-ton::qsent-ack-eliciting rec) (> (- now (cl-ton::qsent-time rec)) 0.3d0))
                     (push (cons pn rec) lost)))
                 (cl-ton::qsp-sent space))
        (dolist (pair lost)
          (remhash (car pair) (cl-ton::qsp-sent space))
          (dolist (range (cl-ton::qsent-crypto (cdr pair)))
            (push range (cl-ton::qsp-crypto-resend space)))
          (dolist (triple (cl-ton::qsent-streams (cdr pair)))
            (let ((stream (gethash (first triple) (qsrv-streams srv))))
              (when stream (push (cons (second triple) (third triple)) (cl-ton::qs-resend stream)))))
          (dolist (id (cl-ton::qsent-fins (cdr pair)))
            (let ((stream (gethash id (qsrv-streams srv))))
              (when stream (setf (cl-ton::qs-fin-sent stream) nil))))))))
  (%qsrv-flush srv now))

(defun %qnet-pump (net client server now)
  (let ((due '()))
    (sb-thread:with-mutex ((qnet-lock net))
      (setf (qnet-queue net) (sort (qnet-queue net) #'< :key #'first))
      (loop while (and (qnet-queue net) (<= (first (first (qnet-queue net))) now)) do
        (push (pop (qnet-queue net)) due)))
    (dolist (item (nreverse due))
      (if (eq (second item) :to-server)
          (%qsrv-receive server (third item) now)
          (cl-ton::quic-receive client (third item) :now now)))
    (%qsrv-tick server now)))

(defun %quic-scenario (&key (drop 0d0) answer-fn (server-seed-byte #x22) (expect-seed-byte server-seed-byte))
  (let* ((net (make-qnet :drop drop))
         (server-seed (make-array 32 :element-type '(unsigned-byte 8) :initial-element server-seed-byte))
         (expect-seed (make-array 32 :element-type '(unsigned-byte 8) :initial-element expect-seed-byte))
         (server (%make-qsrv net :identity-seed server-seed :answer-fn answer-fn))
         (peer-id (cl-ton::adnl-short-id (cl-ton::keypair-public (cl-ton::seed->keypair expect-seed))))
         (client (cl-ton::make-quic-connection
                  (lambda (d) (%qnet-send net :to-server d (cl-ton::rldp-clock)))
                  :identity-seed (make-array 32 :element-type '(unsigned-byte 8) :initial-element #x11)
                  :peer-id peer-id)))
    (values client server net)))

(defun %quic-run-query (client server net data &key (timeout 10))
  (let ((result nil) (failure nil) (done nil))
    (sb-thread:make-thread
     (lambda ()
       (handler-case (setf result (cl-ton::quic-query client data :timeout timeout))
         (error (e) (setf failure e)))
       (setf done t))
     :name "quic-test-query")
    (let ((deadline (+ (cl-ton::rldp-clock) timeout 5)))
      (loop until (or done (> (cl-ton::rldp-clock) deadline)) do
        (%qnet-pump net client server (cl-ton::rldp-clock))
        (sleep 0.002)))
    (values result failure done)))

(defun test-quic-connection ()
  (format t "~&QUIC connection (mock server, simulated network):~%")
  ;; 1. a clean run: handshake + an echo query
  (multiple-value-bind (client server net)
      (%quic-scenario :answer-fn (lambda (d) (cl-ton::concat-octets (list (cl-ton::quic-ascii "answer:") d))))
    (let ((data (cl-ton::quic-ascii "tonNode.getCapabilities")))
      (multiple-value-bind (answer failure done) (%quic-run-query client server net data :timeout 10)
        (check "quic connection echo query answered" (and done (null failure) answer
                                                          (equalp answer (cl-ton::concat-octets
                                                                          (list (cl-ton::quic-ascii "answer:") data)))))
        (check "quic connection established on both ends"
               (and (eq (cl-ton::qc-state client) :established) (qsrv-established server))))))
  ;; 2. a 100 KB answer: many packets, stream reassembly, flow control
  (let ((pattern (make-array 100000 :element-type '(unsigned-byte 8))))
    (dotimes (i 100000) (setf (aref pattern i) (logand (* i 7) 255)))
    (multiple-value-bind (client server net) (%quic-scenario :answer-fn (lambda (d) (declare (ignore d)) pattern))
      (multiple-value-bind (answer failure done) (%quic-run-query client server net (cl-ton::quic-ascii "big") :timeout 20)
        (check "quic connection 100 KB answer intact" (and done (null failure) answer (equalp answer pattern))))))
  ;; 3. a lossy run: 12% of datagrams dropped, jittered delays
  (multiple-value-bind (client server net)
      (%quic-scenario :drop 0.12d0 :answer-fn (lambda (d) (cl-ton::concat-octets (list (cl-ton::quic-ascii "answer:") d))))
    (setf (qnet-jitter net) 0.04d0)
    (let ((data (cl-ton::quic-ascii "tonNode.getCapabilities")))
      (multiple-value-bind (answer failure done) (%quic-run-query client server net data :timeout 25)
        (check "quic connection survives 12% datagram loss" (and done (null failure) answer
                                                                 (equalp answer (cl-ton::concat-octets
                                                                                 (list (cl-ton::quic-ascii "answer:") data))))))))
  ;; 4. a server whose key is not the expected peer: the handshake must be refused
  (multiple-value-bind (client server net) (%quic-scenario :server-seed-byte #x33 :expect-seed-byte #x22)
    (multiple-value-bind (answer failure done) (%quic-run-query client server net (cl-ton::quic-ascii "x") :timeout 10)
      (check "quic connection refuses the wrong peer key"
             (and done failure (null answer) (eq (cl-ton::qc-state client) :failed))))))
