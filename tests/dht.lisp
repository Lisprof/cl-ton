;;;; tests/dht.lisp -- the DHT client (src/dht.lisp) against a small simulated DHT on loopback UDP.
;;;;
;;;; The simulated nodes answer the bare queries of a client as the node's sources say, with signed dht.node entries and signed
;;;; dht.value records, and each knows only a few others, so a search has to walk.  What a REAL node answers can be learned only
;;;; on a real network.

(in-package :cl-ton/test)

(defun %dht-t-now () (cl-ton::unix-now))

(defun %dht-t-address-list (port)
  (cl-ton::tl-make "adnl.addressList"
                   :addrs (list (cl-ton::tl-make "adnl.address.udp" :ip 2130706433 :port port))
                   :version 0 :reinit-date 0 :priority 0 :expire-at 0))

(defun %dht-t-sign (keypair octets) (coerce (cl-ton::sign-octets keypair octets) 'cl-ton::tl-octets))

(defun %dht-t-node (keypair port &key (version 1) network-id)
  "A signed dht.node of KEYPAIR at 127.0.0.1:PORT; NETWORK-ID makes the 68-octet signature form."
  (let* ((pub (cl-ton::tl-make "pub.ed25519" :key (coerce (cl-ton::keypair-public keypair) 'cl-ton::tl-octets)))
         (prefix (if network-id
                     (coerce (reverse (cl-ton::uint->octets network-id 4)) 'cl-ton::tl-octets)
                     (coerce #() 'cl-ton::tl-octets)))
         (to-sign (cl-ton::tl-encode (cl-ton::tl-make "dht.node" :id pub :addr-list (%dht-t-address-list port)
                                                                 :version version :signature prefix)))
         (signature (%dht-t-sign keypair to-sign)))
    (cl-ton::tl-make "dht.node" :id pub :addr-list (%dht-t-address-list port) :version version
                                :signature (coerce (concatenate '(vector (unsigned-byte 8)) prefix signature) 'cl-ton::tl-octets))))

(defun %dht-t-value (keypair data &key (ttl (+ (%dht-t-now) 3600)) (name "address") (index 0) (sign-with keypair))
  "A dht.value under {short id of KEYPAIR, NAME, INDEX} carrying DATA, signed by SIGN-WITH."
  (let* ((pub (cl-ton::tl-make "pub.ed25519" :key (coerce (cl-ton::keypair-public keypair) 'cl-ton::tl-octets)))
         (key (cl-ton::tl-make "dht.key" :id (coerce (cl-ton::adnl-short-id (cl-ton::keypair-public keypair)) 'cl-ton::tl-octets)
                                         :name (coerce (cl-ton::ascii name) 'cl-ton::tl-octets) :idx index))
         (rule (cl-ton::tl-make "dht.updateRule.signature"))
         (empty (coerce #() 'cl-ton::tl-octets))
         (description (cl-ton::tl-make "dht.keyDescription" :key key :id pub :update-rule rule :signature empty))
         (description (cl-ton::tl-make "dht.keyDescription" :key key :id pub :update-rule rule
                                                            :signature (%dht-t-sign sign-with (cl-ton::tl-encode description))))
         (bare (cl-ton::tl-make "dht.value" :key description :value (coerce data 'cl-ton::tl-octets) :ttl ttl :signature empty)))
    (cl-ton::tl-make "dht.value" :key description :value (coerce data 'cl-ton::tl-octets) :ttl ttl
                                 :signature (%dht-t-sign sign-with (cl-ton::tl-encode bare)))))

(defstruct (dht-t-server (:copier nil)) keypair node (table '()) (values (make-hash-table :test 'equalp)))

(defun %dht-t-handler (server log)
  (lambda (query public)
    (declare (ignore public))
    (let ((q (cl-ton::tl-decode query)))
      (push (cl-ton::tl-obj-name q) (car log))
      (flet ((nearest (key)
               (let ((sorted (sort (copy-list (dht-t-server-table server)) #'<
                                   :key (lambda (entry) (cl-ton::dht-distance (cl-ton::adnl-short-id (car entry)) key)))))
                 (cl-ton::tl-make "dht.nodes" :nodes (mapcar #'cdr (subseq sorted 0 (min 6 (length sorted))))))))
        (cond ((cl-ton::tl-is q "dht.ping") (cl-ton::tl-encode (cl-ton::tl-make "dht.pong" :random-id (cl-ton::tl-get q :random-id))))
              ((cl-ton::tl-is q "dht.findNode") (cl-ton::tl-encode (nearest (cl-ton::as-octets (cl-ton::tl-get q :key)))))
              ((cl-ton::tl-is q "dht.findValue")
               (let* ((key (cl-ton::as-octets (cl-ton::tl-get q :key)))
                      (value (gethash key (dht-t-server-values server))))
                 (cl-ton::tl-encode (if value
                                        (cl-ton::tl-make "dht.valueFound" :value value)
                                        (cl-ton::tl-make "dht.valueNotFound" :nodes (nearest key))))))
              (t nil))))))

(defun %dht-t-network (count &key (log (list nil)))
  "COUNT simulated nodes; node I knows nodes I+1, I+2 and I+5 (mod COUNT).  Returns the list of servers."
  (let* ((servers (loop repeat count collect (make-dht-t-server :keypair (cl-ton::adnl-generate-keypair)))))
    (dolist (s servers)
      (setf (dht-t-server-node s) (cl-ton::adnl-udp-start :keypair (dht-t-server-keypair s) :handler (%dht-t-handler s log))))
    (loop for s in servers for i from 0
          do (setf (dht-t-server-table s)
                   (loop for d in '(1 2 5)
                         collect (let ((other (nth (mod (+ i d) count) servers)))
                                   (cons (cl-ton::keypair-public (dht-t-server-keypair other))
                                         (%dht-t-node (dht-t-server-keypair other) (cl-ton::adnl-udp-port (dht-t-server-node other))))))))
    servers))

(defun %dht-t-stop (servers) (dolist (s servers) (cl-ton::adnl-udp-stop (dht-t-server-node s))))

(defun %dht-t-bootstrap-of (servers indexes)
  (loop for i in indexes
        collect (let ((s (nth i servers)))
                  (list (cl-ton::base64-encode (cl-ton::keypair-public (dht-t-server-keypair s))) "127.0.0.1"
                        (cl-ton::adnl-udp-port (dht-t-server-node s))))))

(defun test-dht ()
  (format t "DHT client: signed nodes and values, Kademlia search against simulated nodes~%")
  (let* ((kp (cl-ton::adnl-generate-keypair))
         (other (cl-ton::adnl-generate-keypair))
         (short (cl-ton::adnl-short-id (cl-ton::keypair-public kp))))
    ;; keys
    (check "dht key: the id of {short id, address, 0} is the sha256 of the boxed dht.key; name and index change it"
           (and (equalp (cl-ton::dht-key-id short)
                        (cl-ton::sha256 (cl-ton::tl-encode (cl-ton::tl-make "dht.key" :id (coerce short 'cl-ton::tl-octets)
                                                                                      :name (coerce (cl-ton::ascii "address") 'cl-ton::tl-octets) :idx 0))))
                (not (equalp (cl-ton::dht-key-id short) (cl-ton::dht-key-id short :index 1)))
                (not (equalp (cl-ton::dht-key-id short) (cl-ton::dht-key-id short :name "other")))))
    (check "dht distance: xor, zero to itself, symmetric"
           (and (zerop (cl-ton::dht-distance short short))
                (= (cl-ton::dht-distance short (cl-ton::adnl-short-id (cl-ton::keypair-public other)))
                   (cl-ton::dht-distance (cl-ton::adnl-short-id (cl-ton::keypair-public other)) short))))
    ;; nodes
    (let ((node (%dht-t-node kp 4000)))
      (let ((peer (cl-ton::dht-verify-node node)))
        (check "dht node: a signed node verifies and gives its public key, address and port"
               (and peer (equalp (cl-ton::dht-peer-public peer) (cl-ton::keypair-public kp))
                    (string= "127.0.0.1" (cl-ton::dht-peer-host peer)) (= 4000 (cl-ton::dht-peer-port peer)))))
      (check "dht node: the 68-octet signature (network id + signature) verifies too"
             (cl-ton::dht-verify-node (%dht-t-node kp 4000 :network-id 1234)))
      (check "dht node: an altered port, version or signature is refused"
             (and (null (cl-ton::dht-verify-node (cl-ton::tl-make "dht.node" :id (cl-ton::tl-get node :id) :addr-list (%dht-t-address-list 4001)
                                                                              :version 1 :signature (cl-ton::tl-get node :signature))))
                  (null (cl-ton::dht-verify-node (cl-ton::tl-make "dht.node" :id (cl-ton::tl-get node :id) :addr-list (cl-ton::tl-get node :addr-list)
                                                                              :version 2 :signature (cl-ton::tl-get node :signature))))
                  (null (cl-ton::dht-verify-node (cl-ton::tl-make "dht.node" :id (cl-ton::tl-get node :id) :addr-list (cl-ton::tl-get node :addr-list)
                                                                              :version 1 :signature (%flipped-copy (cl-ton::tl-get node :signature) 3))))))
      (check "dht node: a node without an address is refused"
             (null (cl-ton::dht-verify-node (cl-ton::tl-make "dht.node" :id (cl-ton::tl-get node :id)
                                                                         :addr-list (cl-ton::tl-make "adnl.addressList" :addrs '() :version 0 :reinit-date 0 :priority 0 :expire-at 0)
                                                                         :version 1 :signature (cl-ton::tl-get node :signature))))))
    ;; values
    (let* ((data (cl-ton::tl-encode (%dht-t-address-list 5555)))
           (value (%dht-t-value kp data))
           (key-id (cl-ton::dht-key-id short)))
      (check "dht value: a signed value for the key asked verifies and gives its data and the owner's key"
             (multiple-value-bind (got public) (cl-ton::dht-verify-value value key-id)
               (and got (equalp got data) (equalp public (cl-ton::keypair-public kp)))))
      (check "dht value: the key asked for must be the value's key"
             (null (cl-ton::dht-verify-value value (cl-ton::dht-key-id short :index 1))))
      (check "dht value: an expired value is refused"
             (null (cl-ton::dht-verify-value (%dht-t-value kp data :ttl (- (%dht-t-now) 10)) key-id)))
      (check "dht value: a value signed by another key is refused (the description or the value signature)"
             (null (cl-ton::dht-verify-value (%dht-t-value kp data :sign-with other) key-id)))
      (check "dht value: altered data keeps the old signature and is refused"
             (null (cl-ton::dht-verify-value (cl-ton::tl-make "dht.value" :key (cl-ton::tl-get value :key)
                                                                          :value (coerce (cl-ton::tl-encode (%dht-t-address-list 6666)) 'cl-ton::tl-octets)
                                                                          :ttl (cl-ton::tl-get value :ttl) :signature (cl-ton::tl-get value :signature))
                                             key-id)))
      (check "dht value: a key description that names another owner is refused"
             (let* ((forged-description (cl-ton::tl-make "dht.keyDescription"
                                                         :key (cl-ton::tl-get (cl-ton::tl-get value :key) :key)
                                                         :id (cl-ton::tl-make "pub.ed25519" :key (coerce (cl-ton::keypair-public other) 'cl-ton::tl-octets))
                                                         :update-rule (cl-ton::tl-get (cl-ton::tl-get value :key) :update-rule)
                                                         :signature (cl-ton::tl-get (cl-ton::tl-get value :key) :signature))))
               (null (cl-ton::dht-verify-value (cl-ton::tl-make "dht.value" :key forged-description :value (cl-ton::tl-get value :value)
                                                                            :ttl (cl-ton::tl-get value :ttl) :signature (cl-ton::tl-get value :signature))
                                               key-id)))))))

(defun test-dht-search ()
  (format t "DHT client: a search over a small simulated DHT~%")
  (let* ((log (list nil))
         (servers (%dht-t-network 12 :log log))
         (target (cl-ton::adnl-generate-keypair))
         (target-short (cl-ton::adnl-short-id (cl-ton::keypair-public target)))
         (key-id (cl-ton::dht-key-id target-short))
         (holder (first (sort (copy-list servers) #'<
                              :key (lambda (s) (cl-ton::dht-distance (cl-ton::adnl-short-id (cl-ton::keypair-public (dht-t-server-keypair s))) key-id)))))
         (address-list (%dht-t-address-list 7777))
         (cache (format nil "/tmp/dht-cache-~D.txt" (random 1000000))))
    (setf (gethash key-id (dht-t-server-values holder)) (%dht-t-value target (cl-ton::tl-encode address-list)))
    (unwind-protect
         (let ((dht (cl-ton::dht-start :bootstrap (%dht-t-bootstrap-of servers '(0 3)) :timeout 1.5)))
           (unwind-protect
                (progn
                  (check "dht: the client starts with only its two bootstrap nodes"
                         (= 2 (cl-ton::dht-peer-count dht)))
                  (check "dht ping: a node answers with the random id we sent"
                         (cl-ton::dht-ping dht (first (cl-ton::%dht-nearest dht key-id 1))))
                  (let ((nodes (cl-ton::dht-find-nodes dht key-id)))
                    (check "dht find nodes: the search walks the network and finds the node nearest to the key"
                           (and nodes (> (cl-ton::dht-peer-count dht) 2)
                                (equalp (cl-ton::dht-peer-public (first nodes)) (cl-ton::keypair-public (dht-t-server-keypair holder))))))
                  (check "dht: the client's queries are bare (no dht.query wrapper): the servers saw only plain dht.* queries"
                         (and (car log) (every (lambda (name) (member name '("dht.ping" "dht.findNode" "dht.findValue") :test #'string=)) (car log))))
                  (multiple-value-bind (list public) (cl-ton::dht-find-address dht target-short)
                    (check "dht find address: the verified address list of a node and its public key"
                           (and list public (equalp public (cl-ton::keypair-public target))
                                (multiple-value-bind (host port) (cl-ton::%dht-udp-address list)
                                  (and (string= host "127.0.0.1") (= port 7777))))))
                  (check "dht find value: a key nobody stores is not found"
                         (null (cl-ton::dht-find-value dht (cl-ton::dht-key-id (cl-ton::adnl-short-id (cl-ton::keypair-public (cl-ton::adnl-generate-keypair)))))))
                  (check "dht cache: the nodes that answered are written and a new client can start from them alone"
                         (progn (cl-ton::dht-save-cache dht cache)
                                (let ((again (cl-ton::dht-start :bootstrap '() :cache-file cache :timeout 1.0)))
                                  (unwind-protect
                                       (and (>= (cl-ton::dht-peer-count again) 3)
                                            (cl-ton::dht-find-address again target-short))
                                    (cl-ton::dht-stop again))))))
             (cl-ton::dht-stop dht)))
      (ignore-errors (delete-file cache))
      (%dht-t-stop servers))
    ;; a lying node and dead nodes
    (let* ((servers (%dht-t-network 8))
           (target (cl-ton::adnl-generate-keypair))
           (short (cl-ton::adnl-short-id (cl-ton::keypair-public target)))
           (key-id (cl-ton::dht-key-id short))
           (sorted (sort (copy-list servers) #'<
                         :key (lambda (s) (cl-ton::dht-distance (cl-ton::adnl-short-id (cl-ton::keypair-public (dht-t-server-keypair s))) key-id))))
           (liar (first sorted)) (honest (second sorted)))
      (setf (gethash key-id (dht-t-server-values liar))
            (%dht-t-value target (cl-ton::tl-encode (%dht-t-address-list 1111)) :sign-with (cl-ton::adnl-generate-keypair)))
      (setf (gethash key-id (dht-t-server-values honest))
            (%dht-t-value target (cl-ton::tl-encode (%dht-t-address-list 2222))))
      (unwind-protect
           (let ((dht (cl-ton::dht-start :bootstrap (append '(("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA=" "127.0.0.1" 9))
                                                            (%dht-t-bootstrap-of servers '(0 1)))
                                         :timeout 1.5)))
             (unwind-protect
                  (multiple-value-bind (list public) (cl-ton::dht-find-address dht short)
                    (check "dht: a nearer node that serves a forged value is ignored and the honest value is found"
                           (and list (equalp public (cl-ton::keypair-public target))
                                (= 2222 (nth-value 1 (cl-ton::%dht-udp-address list)))))
                    ;; the search may end before the query to the dead node has timed out: wait for it, then look
                    (sleep 1.8)
                    (check "dht: a dead bootstrap node is tolerated and counted as failing"
                           (let ((dead (gethash (cl-ton::adnl-short-id (cl-ton::base64-decode "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA="))
                                                (cl-ton::dht-peers dht))))
                             (and dead (plusp (cl-ton::dht-peer-failures dead))))))
               (cl-ton::dht-stop dht)))
        (%dht-t-stop servers)))))

;;; --- members of a public overlay (the overlayNodes rule) ---------------------------------------------------------------------------

(defun %dht-t-overlay-node (keypair overlay-id &key (version 1) (sign-with keypair) (overlay overlay-id))
  "A signed overlay.node of KEYPAIR for OVERLAY (the overlay it names) signed by SIGN-WITH over the toSign of OVERLAY-ID."
  (let* ((pub (cl-ton::tl-make "pub.ed25519" :key (coerce (cl-ton::keypair-public keypair) 'cl-ton::tl-octets)))
         (short (cl-ton::adnl-short-id (cl-ton::keypair-public keypair)))
         (to-sign (cl-ton::tl-encode (cl-ton::tl-make "overlay.node.toSign"
                                                      :id (cl-ton::tl-make "adnl.id.short" :id (coerce short 'cl-ton::tl-octets))
                                                      :overlay (coerce overlay-id 'cl-ton::tl-octets) :version version))))
    (cl-ton::tl-make "overlay.node" :id pub :overlay (coerce overlay 'cl-ton::tl-octets) :version version
                                    :signature (%dht-t-sign sign-with to-sign))))

(defun %dht-t-overlay-value (overlay-name nodes &key (signature-octets #()) (rule "dht.updateRule.overlayNodes"))
  "(VALUES VALUE OVERLAY-ID) a dht.value for the overlay-nodes key of the overlay named OVERLAY-NAME, holding NODES."
  (let* ((pub (cl-ton::tl-make "pub.overlay" :name (coerce overlay-name 'cl-ton::tl-octets)))
         (overlay-id (cl-ton::sha256 (cl-ton::tl-encode pub)))
         (key (cl-ton::tl-make "dht.key" :id (coerce overlay-id 'cl-ton::tl-octets) :name (coerce (cl-ton::ascii "nodes") 'cl-ton::tl-octets) :idx 0))
         (description (cl-ton::tl-make "dht.keyDescription" :key key :id pub :update-rule (cl-ton::tl-make rule)
                                                            :signature (coerce #() 'cl-ton::tl-octets))))
    (values (cl-ton::tl-make "dht.value" :key description
                                         :value (coerce (cl-ton::tl-encode (cl-ton::tl-make "overlay.nodes" :nodes nodes)) 'cl-ton::tl-octets)
                                         :ttl (+ (%dht-t-now) 3600)
                                         :signature (coerce signature-octets 'cl-ton::tl-octets))
            overlay-id)))

(defun test-dht-overlay-members ()
  (format t "DHT client: the verified members of a public overlay (dht.updateRule.overlayNodes)~%")
  (let* ((name (ironclad:random-data 32))
         (members (loop repeat 5 collect (cl-ton::adnl-generate-keypair)))
         (stranger (cl-ton::adnl-generate-keypair))
         (other-overlay (ironclad:random-data 32)))
    (multiple-value-bind (probe-value overlay-id) (%dht-t-overlay-value name '())
      (declare (ignore probe-value))
      (let* ((good-nodes (loop for m in members for v from 10 collect (%dht-t-overlay-node m overlay-id :version v)))
             (forged (%dht-t-overlay-node stranger overlay-id :sign-with (first members)))        ; signed by the wrong key
             (foreign (%dht-t-overlay-node stranger overlay-id :overlay other-overlay))             ; names another overlay
             (newer (%dht-t-overlay-node (first members) overlay-id :version 99))
             (key-id (cl-ton::dht-key-id overlay-id :name "nodes")))
        ;; the value check on its own
        (multiple-value-bind (list reason) (cl-ton::dht-overlay-value-nodes (%dht-t-overlay-value name (list* forged foreign good-nodes)) overlay-id)
          (check "overlay nodes: the five honest nodes verify, the forged one and the one of another overlay are dropped"
                 (and (= 5 (length list)) (search "5 of 7" reason)
                      (null (set-difference (mapcar #'car list) (mapcar #'cl-ton::keypair-public members) :test #'equalp))))
          (check "overlay nodes: the versions come from the signed nodes" (equal (sort (mapcar #'cdr list) #'<) '(10 11 12 13 14))))
        (check "overlay nodes: a value that carries a signature is refused"
               (null (cl-ton::dht-overlay-value-nodes (%dht-t-overlay-value name good-nodes :signature-octets (make-array 64 :initial-element 7)) overlay-id)))
        (check "overlay nodes: a value under the signature rule is refused"
               (null (cl-ton::dht-overlay-value-nodes (%dht-t-overlay-value name good-nodes :rule "dht.updateRule.signature") overlay-id)))
        (check "overlay nodes: a value of another overlay is refused"
               (null (cl-ton::dht-overlay-value-nodes (%dht-t-overlay-value other-overlay good-nodes) overlay-id)))
        (check "overlay nodes: a node is not accepted for an overlay it does not name"
               (and (null (cl-ton::dht-verify-overlay-node foreign overlay-id))
                    (null (cl-ton::dht-verify-overlay-node forged overlay-id))
                    (equalp (cl-ton::dht-verify-overlay-node (first good-nodes) overlay-id) (cl-ton::keypair-public (first members)))))
        ;; the search over a simulated DHT: two holders of different parts of the member list
        (let* ((servers (%dht-t-network 12))
               (sorted (sort (copy-list servers) #'<
                             :key (lambda (s) (cl-ton::dht-distance (cl-ton::adnl-short-id (cl-ton::keypair-public (dht-t-server-keypair s))) key-id))))
               (a (first sorted)) (b (second sorted)))
          (setf (gethash key-id (dht-t-server-values a)) (%dht-t-overlay-value name (list* forged (subseq good-nodes 0 3))))
          (setf (gethash key-id (dht-t-server-values b)) (%dht-t-overlay-value name (list* newer foreign (subseq good-nodes 2))))
          (unwind-protect
               (let ((dht (cl-ton::dht-start :bootstrap (%dht-t-bootstrap-of servers '(0 3)) :timeout 1.5)))
                 (unwind-protect
                      (multiple-value-bind (found notes) (cl-ton::dht-find-overlay-members dht overlay-id :want 100)
                        (check "overlay members: the five honest members are found, merged over both holders, each once"
                               (and (= 5 (length found))
                                    (null (set-difference (mapcar #'car found) (mapcar #'cl-ton::keypair-public members) :test #'equalp))))
                        (check "overlay members: the newest signed version of a member wins"
                               (= 99 (cdr (find (cl-ton::keypair-public (first members)) found :key #'car :test #'equalp))))
                        (check "overlay members: the notes tell what the nodes said" (and notes (every #'stringp notes))))
                   (cl-ton::dht-stop dht)))
            (%dht-t-stop servers)))
        ;; the address summary
        (let ((list (cl-ton::tl-make "adnl.addressList"
                                     :addrs (list (cl-ton::tl-make "adnl.address.udp" :ip (+ (ash 10 24) (ash 1 16) (ash 2 8) 3) :port 3000)
                                                  (cl-ton::tl-make "adnl.address.quic" :ip (+ (ash 10 24) (ash 1 16) (ash 2 8) 3) :port 4000))
                                     :version 0 :reinit-date 0 :priority 0 :expire-at 0)))
          (multiple-value-bind (strings qh qp uh up) (cl-ton::adnl-address-summary list)
            (check "address summary: the udp and quic endpoints of an address list"
                   (and (equal strings '("udp 10.1.2.3:3000" "quic 10.1.2.3:4000")) (string= qh "10.1.2.3") (= qp 4000)
                        (string= uh "10.1.2.3") (= up 3000)))))))))

;;; --- peers of a public overlay: members, then their signed address lists ---------------------------------------------------------

(defun test-dht-overlay-peers ()
  (format t "DHT client: the peers of a public overlay (members resolved through their address lists)~%")
  (let* ((name (ironclad:random-data 32))
         (members (loop repeat 4 collect (cl-ton::adnl-generate-keypair)))   ; the fourth has no address record
         (overlay-id (nth-value 1 (%dht-t-overlay-value name '())))
         (nodes (loop for m in members for v from 1 collect (%dht-t-overlay-node m overlay-id :version v)))
         (servers (%dht-t-network 12)))
    (flet ((put (key-id value)
             (let ((holder (first (sort (copy-list servers) #'<
                                        :key (lambda (s) (cl-ton::dht-distance (cl-ton::adnl-short-id (cl-ton::keypair-public (dht-t-server-keypair s))) key-id))))))
               (setf (gethash key-id (dht-t-server-values holder)) value))))
      (put (cl-ton::dht-key-id overlay-id :name "nodes") (%dht-t-overlay-value name nodes))
      (loop for m in (subseq members 0 3) for port from 7001
            do (put (cl-ton::dht-key-id (cl-ton::adnl-short-id (cl-ton::keypair-public m)))
                    (%dht-t-value m (cl-ton::tl-encode (%dht-t-address-list port))))))
    (unwind-protect
         (let ((dht (cl-ton::dht-start :bootstrap (%dht-t-bootstrap-of servers '(0 3)) :timeout 1.5)))
           (unwind-protect
                (progn
                  (multiple-value-bind (peers found notes) (cl-ton::dht-overlay-peers dht overlay-id :max 10)
                    (check "overlay peers: the DHT nodes' answers come back as notes" (and notes (every #'stringp notes)))
                    (check "overlay peers: four verified members, the three with an address record become peers (127.0.0.1, their ports, their keys)"
                           (and (= 4 found) (= 3 (length peers))
                                (every (lambda (p) (string= "127.0.0.1" (first p))) peers)
                                (equal (sort (mapcar #'second peers) #'<) '(7001 7002 7003))
                                (null (set-difference (mapcar #'third peers) (mapcar #'cl-ton::keypair-public (subseq members 0 3)) :test #'equalp)))))
                  (check "overlay peers: MAX limits the list"
                         (= 2 (length (cl-ton::dht-overlay-peers dht overlay-id :max 2))))
                  (check "overlay peers: an overlay nobody publishes has no peers"
                         (multiple-value-bind (peers found)
                             (cl-ton::dht-overlay-peers dht (cl-ton::sha256 (ironclad:random-data 8)))
                           (and (null peers) (zerop found)))))
             (cl-ton::dht-stop dht)))
      (%dht-t-stop servers))))
