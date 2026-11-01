;;;; tests/adnl-udp.lisp -- ADNL over UDP (src/adnl-udp.lisp).
;;;;
;;;; No other implementation of the UDP side is available offline, so these tests pin down what the node's sources say
;;;; (layout, key derivation, what the signature covers, replay rules) and run a client and a server of this library
;;;; against each other on loopback.  A real node answers or does not: that is the job of the DHT probe on a real network.

(in-package :cl-ton/test)

(defun %udp-server (&optional (handler (lambda (query public) (declare (ignore public)) (cl-ton::%cat (map 'vector #'char-code "re:") query))))
  (cl-ton::adnl-udp-start :handler handler))

(defun test-adnl-udp ()
  (format t "ADNL over UDP: datagrams, signed packets, replay rules, queries~%")
  (let* ((server (cl-ton::adnl-generate-keypair))
         (client (cl-ton::adnl-generate-keypair))
         (plain (map '(vector (unsigned-byte 8)) #'char-code "a short plain text of some length"))
         (message (cl-ton::adnl-udp-encrypt (cl-ton::keypair-public server) plain)))
    ;; the encrypted message
    (check "udp crypto: ephemeral key (32) + digest (32) + ciphertext of the plain text's length"
           (= (length message) (+ 64 (length plain))))
    (check "udp crypto: the digest is the sha256 of the plain text and the plain text is not in the message"
           (and (equalp (subseq message 32 64) (cl-ton::sha256 plain))
                (null (search plain message))))
    (check "udp crypto: the owner of the key decrypts it"
           (equalp plain (cl-ton::adnl-udp-decrypt server message)))
    (check "udp crypto: another key does not"
           (handler-case (progn (cl-ton::adnl-udp-decrypt client message) nil) (cl-ton:ton-error () t)))
    (check "udp crypto: a flipped ciphertext octet is refused"
           (handler-case (progn (cl-ton::adnl-udp-decrypt server (%flipped-copy message 70)) nil) (cl-ton:ton-error () t)))
    (check "udp crypto: two encryptions of one text differ (a fresh ephemeral key each time)"
           (not (equalp message (cl-ton::adnl-udp-encrypt (cl-ton::keypair-public server) plain))))
    ;; the datagram
    (let ((datagram (cl-ton::adnl-udp-datagram (cl-ton::keypair-public server) plain)))
      (check "udp datagram: starts with the short id of the receiver, 32 octets, then the message"
             (and (equalp (subseq datagram 0 32) (cl-ton::adnl-short-id (cl-ton::keypair-public server)))
                  (= (length datagram) (+ 32 64 (length plain)))))
      (check "udp datagram: opens for its receiver"
             (equalp plain (cl-ton::adnl-udp-open-datagram server datagram)))
      (check "udp datagram: is refused by a node it is not addressed to"
             (handler-case (progn (cl-ton::adnl-udp-open-datagram client datagram) nil) (cl-ton:ton-error () t))))
    ;; the signed packet
    (let* ((query (cl-ton::tl-make "adnl.message.query" :query-id (make-array 32 :element-type '(unsigned-byte 8) :initial-element 3)
                                                        :query (coerce #(1 2 3) 'cl-ton::tl-octets)))
           (packet (cl-ton::adnl-udp-make-packet client (list query) :seqno 1 :confirm-seqno 0 :reinit-date 1700000000
                                                 :address (cl-ton::adnl-udp-address-list))))
      (multiple-value-bind (decoded public) (cl-ton::adnl-udp-open-packet packet)
        (check "udp packet: signed with the sender's key, which it names"
               (equalp public (cl-ton::keypair-public client)))
        (check "udp packet: one message, seqno, reinit date and an address list without an address"
               (and (= 1 (length (cl-ton::adnl-udp-packet-messages decoded)))
                    (= 1 (cl-ton::tl-get decoded :seqno))
                    (= 1700000000 (cl-ton::tl-get decoded :reinit-date))
                    (zerop (length (cl-ton::tl-get (cl-ton::tl-get decoded :address) :addrs))))))
      (check "udp packet: the signature covers the packet without the signature"
             (let ((decoded (cl-ton::tl-decode packet)))
               (ironclad:verify-signature (ironclad:make-public-key :ed25519 :y (cl-ton::keypair-public client))
                                          (cl-ton::adnl-udp-packet-to-sign decoded)
                                          (cl-ton::as-octets (cl-ton::tl-get decoded :signature)))))
      (check "udp packet: an altered octet in the message breaks the signature"
             (handler-case (progn (cl-ton::adnl-udp-open-packet (%flipped-copy packet 60)) nil) (error () t)))
      (check "udp packet: a packet signed by another key than the one it names is refused"
             (let* ((forged (cl-ton::tl-decode packet))
                    (other (cl-ton::adnl-generate-keypair))
                    (bad (cl-ton::tl-make "adnl.packetContents"
                                          :rand1 (cl-ton::tl-get forged :rand1) :flags (cl-ton::tl-get forged :flags)
                                          :from (cl-ton::tl-get forged :from) :message (cl-ton::tl-get forged :message)
                                          :address (cl-ton::tl-get forged :address) :seqno 1 :confirm-seqno 0
                                          :reinit-date 1700000000 :dst-reinit-date 0
                                          :signature (coerce (cl-ton::sign-octets other (cl-ton::adnl-udp-packet-to-sign forged)) 'cl-ton::tl-octets)
                                          :rand2 (cl-ton::tl-get forged :rand2))))
               (handler-case (progn (cl-ton::adnl-udp-open-packet (cl-ton::tl-encode bad)) nil) (error () t)))))
    ;; a client and a server on loopback
    (let ((srv (%udp-server)) (cli (cl-ton::adnl-udp-start)))
      (unwind-protect
           (let ((public (cl-ton::keypair-public (cl-ton::adnl-udp-keypair srv)))
                 (port (cl-ton::adnl-udp-port srv)))
             (check "udp query: the server's answer comes back to a client with no public address"
                    (equalp (map '(vector (unsigned-byte 8)) #'char-code "re:ping")
                            (cl-ton::adnl-udp-query cli "127.0.0.1" port public (map '(vector (unsigned-byte 8)) #'char-code "ping")
                                                    :timeout 5)))
             (check "udp query: a second query on the same pair works (seqno moves on)"
                    (equalp (map '(vector (unsigned-byte 8)) #'char-code "re:again")
                            (cl-ton::adnl-udp-query cli "127.0.0.1" port public (map '(vector (unsigned-byte 8)) #'char-code "again")
                                                    :timeout 5)))
             (check "udp query: the server learned the client's key and the source address from the datagram"
                    (let ((peer (gethash (cl-ton::adnl-short-id (cl-ton::keypair-public (cl-ton::adnl-udp-keypair cli)))
                                         (cl-ton::adnl-udp-peers srv))))
                      (and peer (= (cl-ton::adnl-udp-port cli) (cl-ton::adnl-udp-peer-port peer))
                           (>= (cl-ton::adnl-udp-peer-in-seqno peer) 2))))
             (check "udp query: a query to a key the server does not own gets no answer"
                    (handler-case (progn (cl-ton::adnl-udp-query cli "127.0.0.1" port (cl-ton::keypair-public (cl-ton::adnl-generate-keypair))
                                                                 (coerce #(1) '(vector (unsigned-byte 8))) :timeout 0.6)
                                         nil)
                      (cl-ton::adnl-udp-timeout () t)))
             (check "udp query: a server that stays silent ends in a timeout"
                    (let ((quiet (%udp-server (lambda (q p) (declare (ignore q p)) nil))))
                      (unwind-protect
                           (handler-case (progn (cl-ton::adnl-udp-query cli "127.0.0.1" (cl-ton::adnl-udp-port quiet)
                                                                        (cl-ton::keypair-public (cl-ton::adnl-udp-keypair quiet))
                                                                        (coerce #(1) '(vector (unsigned-byte 8))) :timeout 0.6)
                                                 nil)
                             (cl-ton::adnl-udp-timeout () t))
                        (cl-ton::adnl-udp-stop quiet))))
             (check "udp query: a replayed datagram is dropped (the handler runs once)"
                    (let* ((count 0)
                           (counting (%udp-server (lambda (q p) (declare (ignore p)) (incf count) q)))
                           (cpub (cl-ton::keypair-public (cl-ton::adnl-udp-keypair counting)))
                           (kp (cl-ton::adnl-generate-keypair))
                           (sock (make-instance 'sb-bsd-sockets:inet-socket :type :datagram :protocol :udp))
                           (plain (cl-ton::adnl-udp-make-packet
                                   kp (list (cl-ton::tl-make "adnl.message.query" :query-id (make-array 32 :element-type '(unsigned-byte 8) :initial-element 9)
                                                                                    :query (coerce #(7) 'cl-ton::tl-octets)))
                                   :seqno 1 :confirm-seqno 0 :reinit-date (cl-ton::unix-now))))
                      (unwind-protect
                           (let ((datagram (cl-ton::adnl-udp-datagram cpub plain)))
                             (dotimes (i 2)
                               (sb-bsd-sockets:socket-send sock datagram nil
                                                           :address (list (sb-bsd-sockets:make-inet-address "127.0.0.1") (cl-ton::adnl-udp-port counting))))
                             (sleep 0.5)
                             (= 1 count))
                        (ignore-errors (sb-bsd-sockets:socket-close sock))
                        (cl-ton::adnl-udp-stop counting))))
             (check "udp query: garbage datagrams are counted and dropped, the node goes on"
                    (progn (let ((sock (make-instance 'sb-bsd-sockets:inet-socket :type :datagram :protocol :udp)))
                             (sb-bsd-sockets:socket-send sock (make-array 200 :element-type '(unsigned-byte 8) :initial-element 1) nil
                                                         :address (list (sb-bsd-sockets:make-inet-address "127.0.0.1") port))
                             (sb-bsd-sockets:socket-close sock))
                           (sleep 0.3)
                           (and (plusp (cl-ton::adnl-udp-dropped srv))
                                (equalp (map '(vector (unsigned-byte 8)) #'char-code "re:x")
                                        (cl-ton::adnl-udp-query cli "127.0.0.1" port public (map '(vector (unsigned-byte 8)) #'char-code "x")
                                                                :timeout 5))))))
        (cl-ton::adnl-udp-stop cli)
        (cl-ton::adnl-udp-stop srv)))))

(defun %udp-octets (string) (map '(vector (unsigned-byte 8)) #'char-code string))

(defun test-adnl-udp-channels ()
  (format t "ADNL over UDP: channels, parts, peer statistics~%")
  ;; the key schedule of adnl-channel.cpp
  (let* ((a-id (cl-ton::adnl-short-id (cl-ton::keypair-public (cl-ton::adnl-generate-keypair))))
         (b-id (cl-ton::adnl-short-id (cl-ton::keypair-public (cl-ton::adnl-generate-keypair))))
         (a-ch (cl-ton::adnl-generate-keypair))
         (b-ch (cl-ton::adnl-generate-keypair)))
    (check "channel keys: ids are ordered octet by octet"
           (and (cl-ton::adnl-udp-id< (coerce #(1 2 3) 'vector) (coerce #(1 2 4) 'vector))
                (not (cl-ton::adnl-udp-id< (coerce #(1 2 4) 'vector) (coerce #(1 2 3) 'vector)))
                (not (cl-ton::adnl-udp-id< a-id a-id))))
    (multiple-value-bind (a-in a-out) (cl-ton::adnl-udp-channel-keys a-id b-id (cl-ton::keypair-secret a-ch) (cl-ton::keypair-public b-ch))
      (multiple-value-bind (b-in b-out) (cl-ton::adnl-udp-channel-keys b-id a-id (cl-ton::keypair-secret b-ch) (cl-ton::keypair-public a-ch))
        (check "channel keys: what one side sends with (OUT) the other receives with (IN), both ways"
               (and (equalp a-out b-in) (equalp a-in b-out) (not (equalp a-in a-out))))
        (check "channel keys: the ids of the two directions differ and match across the sides"
               (and (equalp (cl-ton::adnl-udp-channel-id a-out) (cl-ton::adnl-udp-channel-id b-in))
                    (not (equalp (cl-ton::adnl-udp-channel-id a-in) (cl-ton::adnl-udp-channel-id a-out)))))
        (check "channel id: the sha256 of the boxed pub.aes of the key"
               (equalp (cl-ton::adnl-udp-channel-id a-out)
                       (cl-ton::sha256 (cl-ton::tl-encode (cl-ton::tl-make "pub.aes" :key (coerce a-out 'cl-ton::tl-octets))))))
        (let ((message (cl-ton::adnl-udp-aes-encrypt a-out (%udp-octets "channel text"))))
          (check "channel AES: the other side decrypts, a flipped octet or another key is refused"
                 (and (equalp (%udp-octets "channel text") (cl-ton::adnl-udp-aes-decrypt b-in message))
                      (handler-case (progn (cl-ton::adnl-udp-aes-decrypt b-in (%flipped-copy message 40)) nil) (cl-ton:ton-error () t))
                      (handler-case (progn (cl-ton::adnl-udp-aes-decrypt a-in message) nil) (cl-ton:ton-error () t)))))))
    (check "channel keys: equal ids use the shared secret for both directions"
           (multiple-value-bind (in out) (cl-ton::adnl-udp-channel-keys a-id a-id (cl-ton::keypair-secret a-ch) (cl-ton::keypair-public b-ch))
             (equalp in out))))
  ;; a channel and big messages between two nodes
  (let* ((count 0)
         (srv (%udp-server (lambda (q p) (declare (ignore p)) (incf count) q)))
         (cli (cl-ton::adnl-udp-start))
         (public (cl-ton::keypair-public (cl-ton::adnl-udp-keypair srv)))
         (port (cl-ton::adnl-udp-port srv)))
    (unwind-protect
         (progn
           (check "channel: the first query is signed, carries createChannel, and the answer confirms the channel"
                  (and (equalp (%udp-octets "one") (cl-ton::adnl-udp-query cli "127.0.0.1" port public (%udp-octets "one") :timeout 5))
                       (let ((peer (cl-ton::adnl-udp-peer-of cli public)))
                         (and (cl-ton::adnl-udp-peer-channel-inited peer) (cl-ton::adnl-udp-peer-channel-ready peer)))
                       (zerop (cl-ton::adnl-udp-channel-packets srv))))
           (check "channel: the second query travels through the channel, the server marks it ready"
                  (and (equalp (%udp-octets "two") (cl-ton::adnl-udp-query cli "127.0.0.1" port public (%udp-octets "two") :timeout 5))
                       (plusp (cl-ton::adnl-udp-channel-packets srv))
                       (let ((peer (cl-ton::adnl-udp-peer-of srv (cl-ton::keypair-public (cl-ton::adnl-udp-keypair cli)))))
                         (and (cl-ton::adnl-udp-peer-channel-ready peer)
                              (equalp (cl-ton::adnl-udp-peer-in-id peer)
                                      (cl-ton::adnl-udp-peer-out-id (cl-ton::adnl-udp-peer-of cli public)))))))
           (check "channel: the answers came back through the channel too (the client counted channel packets)"
                  (plusp (cl-ton::adnl-udp-channel-packets cli)))
           ;; parts, both ways
           (let ((big (make-array 5000 :element-type '(unsigned-byte 8))))
             (dotimes (i 5000) (setf (aref big i) (mod (* i 7) 256)))
             (check "parts: a 5000 octet query and its 5000 octet answer are cut in pieces and put together again"
                    (equalp big (cl-ton::adnl-udp-query cli "127.0.0.1" port public big :timeout 8))))
           (check "parts: a message above 8 KB is refused before anything is sent"
                  (handler-case (progn (cl-ton::adnl-udp-query cli "127.0.0.1" port public (make-array 9000 :element-type '(unsigned-byte 8)) :timeout 1) nil)
                    (cl-ton:ton-error (e) (not (typep e 'cl-ton::adnl-udp-timeout)))))
           (check "parts: pieces whose hash does not match are not delivered"
                  (let* ((before count)
                         (peer (cl-ton::adnl-udp-peer-of cli public))
                         (inner (cl-ton::tl-encode (cl-ton::tl-make "adnl.message.query"
                                                                    :query-id (make-array 32 :element-type '(unsigned-byte 8) :initial-element 4)
                                                                    :query (coerce (make-array 1500 :element-type '(unsigned-byte 8) :initial-element 1) 'cl-ton::tl-octets))))
                         (wrong-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 5)))
                    (loop for offset from 0 below (length inner) by 1024
                          do (cl-ton::%adnl-udp-send-packet
                              cli peer (list (cl-ton::tl-make "adnl.message.part" :hash (coerce wrong-hash 'cl-ton::tl-octets)
                                                                                  :total-size (length inner) :offset offset
                                                                                  :data (coerce (subseq inner offset (min (length inner) (+ offset 1024))) 'cl-ton::tl-octets)))))
                    (sleep 0.4)
                    (= before count)))
           (check "channel: a replayed channel datagram is dropped (the handler runs once for it)"
                  (let* ((peer (cl-ton::adnl-udp-peer-of cli public))
                         (before count)
                         (sock (make-instance 'sb-bsd-sockets:inet-socket :type :datagram :protocol :udp))
                         (packet (cl-ton::adnl-udp-make-channel-packet
                                  (list (cl-ton::tl-make "adnl.message.query"
                                                         :query-id (make-array 32 :element-type '(unsigned-byte 8) :initial-element 8)
                                                         :query (coerce #(9) 'cl-ton::tl-octets)))
                                  :seqno 100000 :confirm-seqno 0))
                         (datagram (cl-ton::%cat (cl-ton::adnl-udp-peer-out-id peer) (cl-ton::adnl-udp-aes-encrypt (cl-ton::adnl-udp-peer-out-key peer) packet))))
                    (unwind-protect
                         (progn (dotimes (i 2)
                                  (sb-bsd-sockets:socket-send sock datagram nil
                                                              :address (list (sb-bsd-sockets:make-inet-address "127.0.0.1") port)))
                                (sleep 0.4)
                                (= (1+ before) count))
                      (ignore-errors (sb-bsd-sockets:socket-close sock)))))
           (check "channel: a datagram for an id that is neither the node's nor a channel's is dropped"
                  (let ((dropped (cl-ton::adnl-udp-dropped srv))
                        (sock (make-instance 'sb-bsd-sockets:inet-socket :type :datagram :protocol :udp)))
                    (unwind-protect
                         (progn (sb-bsd-sockets:socket-send sock (make-array 200 :element-type '(unsigned-byte 8) :initial-element 3) nil
                                                            :address (list (sb-bsd-sockets:make-inet-address "127.0.0.1") port))
                                (sleep 0.3)
                                (> (cl-ton::adnl-udp-dropped srv) dropped))
                      (ignore-errors (sb-bsd-sockets:socket-close sock)))))
           (check "peer statistics: a smoothed round trip time and the answers counted, no failures yet"
                  (let ((peer (cl-ton::adnl-udp-peer-of cli public)))
                    (and (cl-ton::adnl-udp-peer-rtt peer) (< 0 (cl-ton::adnl-udp-peer-rtt peer) 1)
                         (>= (cl-ton::adnl-udp-peer-answers peer) 3)
                         (zerop (cl-ton::adnl-udp-peer-failures peer)))))
           (check "peer statistics: a timeout counts as a failure of that peer"
                  (let ((quiet (%udp-server (lambda (q p) (declare (ignore q p)) nil))))
                    (unwind-protect
                         (let ((qpub (cl-ton::keypair-public (cl-ton::adnl-udp-keypair quiet))))
                           (handler-case (cl-ton::adnl-udp-query cli "127.0.0.1" (cl-ton::adnl-udp-port quiet) qpub (%udp-octets "x") :timeout 0.5)
                             (cl-ton::adnl-udp-timeout () nil))
                           (= 1 (cl-ton::adnl-udp-peer-failures (cl-ton::adnl-udp-peer-of cli qpub))))
                      (cl-ton::adnl-udp-stop quiet)))))
      (cl-ton::adnl-udp-stop cli)
      (cl-ton::adnl-udp-stop srv))))
