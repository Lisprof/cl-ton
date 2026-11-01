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

;;;; dht.lisp -- a client of the TON DHT (Kademlia over ADNL UDP).
;;;;
;;;; From the node's own sources (dht/dht.cpp, dht-query.cpp, dht-node.cpp, dht-types.cpp):
;;;;  * a CLIENT sends the bare query (dht.findNode / dht.findValue / dht.ping), no dht.query wrapper, and announces nothing;
;;;;  * the key of a value is the sha256 of the boxed dht.key {id, name, idx}; the address of an ADNL node is stored under
;;;;    {its short id, "address", 0} as a serialized adnl.addressList;
;;;;  * nearness is the XOR of the 256-bit key and the 256-bit short id of a node;
;;;;  * a dht.node is signed by its own key (over the boxed node with an EMPTY signature; a 68-octet signature is a 4-octet
;;;;    network id and 64 octets, and the signed node then carries those 4 octets as its signature);
;;;;  * a dht.value carries a dht.keyDescription signed by the key's owner (over it with an empty signature) and its own
;;;;    signature by the same key (over the boxed value with an empty signature), and a ttl that is the unix time it expires.
;;;; Nothing an answer says is believed before its signatures are checked.  The search asks the A nearest unqueried nodes of the
;;;; K nearest known ones in parallel, adds every verified node an answer names, and stops when the K nearest have all answered.

(in-package :cl-ton)

(defparameter *dht-bootstrap*
  '(
    ("gzUNJnBJhdpooYCE8juKZo2y4tYDIQfoCvFm0yBr7y0=" "5.78.60.12" 54390)
    ("jXiLaOQz1HPayilWgBWhV9xJhUIqfU95t+KFKQPIpXg=" "5.161.60.160" 12485)
    ("vhFPq+tgjJi+4ZbEOHBo4qjpqhBdSCzNZBdgXyj3NK8=" "5.22.218.95" 36752)
    ("sbsuMcdyYFSRQ0sG86/n+ZQ5FX3zOWm1aCVuHwXdgs0=" "45.63.114.174" 50187)
    ("aeMgdMdkkbkfAS4+n4BEGgtqhkf2/zXrVWWECOJ/h3A=" "167.172.48.179" 25975))
  "The only static seed: five public DHT nodes of the mainnet (public key in base64, IPv4, UDP port), from the global config.")

(defconstant +dht-k+ 10 "How many nearest nodes a search keeps and asks for.")
(defconstant +dht-a+ 3 "How many queries of a search run at once.")
(defconstant +dht-max-name+ 127)
(defconstant +dht-max-index+ 15)
(defconstant +dht-max-value+ 4096)

;;; --- keys, distance ------------------------------------------------------------------------------------------------------------------

(defun dht-key-id (id &key (name "address") (index 0))
  "The 32-octet id of the DHT key {ID, NAME, INDEX}: sha256 of the boxed dht.key; ID is a 32-octet short id."
  (sha256 (tl-encode (tl-make "dht.key" :id (coerce id 'tl-octets) :name (coerce (ascii name) 'tl-octets) :idx index))))

(defun dht-distance (a b)
  "The Kademlia distance of two 32-octet ids: their XOR as an integer."
  (logxor (octets->uint a) (octets->uint b)))

;;; --- signed nodes and values -----------------------------------------------------------------------------------------------------

(defstruct (dht-peer (:copier nil))
  public short-id host port
  (version 0) (rtt nil) (failures 0) (answers 0))

(defun %dht-udp-address (address-list)
  "(VALUES HOST PORT) of the first IPv4 UDP address of an adnl.addressList, or NIL."
  (loop for a across (coerce (tl-get address-list :addrs) 'vector)
        when (tl-is a "adnl.address.udp")
          do (let ((ip (ldb (byte 32 0) (tl-get a :ip))))
               (return (values (format nil "~D.~D.~D.~D" (ldb (byte 8 24) ip) (ldb (byte 8 16) ip) (ldb (byte 8 8) ip) (ldb (byte 8 0) ip))
                               (tl-get a :port))))))

(defun %dht-verify-signature (public message signature)
  (and (= 32 (length public)) (= 64 (length signature))
       (ignore-errors
        (ironclad:verify-signature (ironclad:make-public-key :ed25519 :y public) (as-octets message) (as-octets signature)))))

(defun dht-node-to-sign (node)
  "The octets a dht.node's signature covers (see the file header for the network id form)."
  (let* ((sig (as-octets (tl-get node :signature)))
         (prefix (if (= (length sig) 68) (subseq sig 0 4) (make-array 0 :element-type '(unsigned-byte 8)))))
    (tl-encode (tl-make "dht.node" :id (tl-get node :id) :addr-list (tl-get node :addr-list) :version (tl-get node :version)
                                   :signature (coerce prefix 'tl-octets)))))

(defun dht-verify-node (node)
  "A DHT-PEER for a decoded dht.node whose signature is good, that has a public UDP address; NIL otherwise."
  (ignore-errors
   (let ((sig (as-octets (tl-get node :signature)))
         (id (tl-get node :id)))
     (when (and (tl-is id "pub.ed25519") (member (length sig) '(64 68)))
       (let ((public (as-octets (tl-get id :key))))
         (multiple-value-bind (host port) (%dht-udp-address (tl-get node :addr-list))
           (when (and host (%dht-verify-signature public (dht-node-to-sign node) (subseq sig (- (length sig) 64))))
             (make-dht-peer :public public :short-id (adnl-short-id public) :host host :port port
                            :version (tl-get node :version)))))))))

(defun dht-verify-value (value key-id &key (now (unix-now)))
  "(VALUES VALUE-OCTETS PUBLIC-KEY DESCRIPTION-ID) of a decoded dht.value that is for the key KEY-ID, whose key description and
value are signed by the key's owner and that has not expired; NIL when anything is wrong."
  (ignore-errors
   (let* ((description (tl-get value :key))
          (key (tl-get description :key))
          (pub (tl-get description :id))
          (rule (tl-get description :update-rule))
          (data (as-octets (tl-get value :value))))
     (when (and (tl-is pub "pub.ed25519")
                (tl-is rule "dht.updateRule.signature")
                (<= 1 (length (as-octets (tl-get key :name))) +dht-max-name+)
                (<= 0 (tl-get key :idx) +dht-max-index+)
                (<= (length data) +dht-max-value+)
                (> (tl-get value :ttl) now)
                ;; the key of the value is the one asked for, and it belongs to the owner of the signing key
                (equalp (sha256 (tl-encode key)) (as-octets key-id))
                (equalp (as-octets (tl-get key :id)) (adnl-short-id (as-octets (tl-get pub :key)))))
       (let ((public (as-octets (tl-get pub :key))))
         (when (and (%dht-verify-signature
                     public
                     (tl-encode (tl-make "dht.keyDescription" :key key :id pub :update-rule rule :signature (coerce #() 'tl-octets)))
                     (tl-get description :signature))
                    (%dht-verify-signature
                     public
                     (tl-encode (tl-make "dht.value" :key description :value (tl-get value :value) :ttl (tl-get value :ttl)
                                                     :signature (coerce #() 'tl-octets)))
                     (tl-get value :signature)))
           (values data public (as-octets (tl-get key :id)))))))))

;;; --- the client -------------------------------------------------------------------------------------------------------------------------

(defstruct (dht (:constructor %make-dht) (:copier nil))
  adnl                                  ; the ADNL UDP node the queries go out of
  (peers (make-hash-table :test 'equalp)) ; short id -> dht-peer
  (lock (sb-thread:make-mutex :name "dht"))
  (timeout 2.0)                          ; seconds a node gets for one query
  (queries 0))

(defun %dht-add-peer (dht peer)
  "Remember PEER unless a node with its id is known (a newer version of the same node replaces it)."
  (sb-thread:with-mutex ((dht-lock dht))
    (let ((old (gethash (dht-peer-short-id peer) (dht-peers dht))))
      (cond ((null old) (setf (gethash (dht-peer-short-id peer) (dht-peers dht)) peer) t)
            ((> (dht-peer-version peer) (dht-peer-version old))
             (setf (dht-peer-version old) (dht-peer-version peer) (dht-peer-host old) (dht-peer-host peer)
                   (dht-peer-port old) (dht-peer-port peer))
             nil)
            (t nil)))))

(defun dht-peer-count (dht) (hash-table-count (dht-peers dht)))

(defun dht-start (&key (bootstrap *dht-bootstrap*) adnl (timeout 2.0) cache-file)
  "A DHT client: its own ADNL UDP node (or ADNL), the BOOTSTRAP nodes (public key base64, host, port) and what CACHE-FILE
remembers of an earlier run."
  (let ((dht (%make-dht :adnl (or adnl (adnl-udp-start)) :timeout timeout)))
    (dolist (b bootstrap)
      (destructuring-bind (key host port) b
        (let ((public (base64-decode key)))
          (%dht-add-peer dht (make-dht-peer :public public :short-id (adnl-short-id public) :host host :port port)))))
    (when cache-file (dht-load-cache dht cache-file))
    dht))

(defun dht-stop (dht)
  (adnl-udp-stop (dht-adnl dht)))

(defun %dht-ask (dht peer query)
  "The decoded answer of PEER to the TL object QUERY (sent bare, as a client does), or NIL; the peer's statistics follow."
  (handler-case
      (let* ((start (get-internal-real-time))
             (answer (adnl-udp-query (dht-adnl dht) (dht-peer-host peer) (dht-peer-port peer) (dht-peer-public peer)
                                     (tl-encode query) :timeout (dht-timeout dht)))
             (rtt (/ (- (get-internal-real-time) start) internal-time-units-per-second)))
        (sb-thread:with-mutex ((dht-lock dht))
          (incf (dht-queries dht))
          (incf (dht-peer-answers peer))
          (setf (dht-peer-failures peer) 0
                (dht-peer-rtt peer) (if (dht-peer-rtt peer) (+ (* 0.7 (dht-peer-rtt peer)) (* 0.3 rtt)) rtt)))
        (tl-decode answer))
    (adnl-udp-timeout ()
      (sb-thread:with-mutex ((dht-lock dht)) (incf (dht-queries dht)) (incf (dht-peer-failures peer)))
      nil)
    (error () (sb-thread:with-mutex ((dht-lock dht)) (incf (dht-peer-failures peer))) nil)))

(defun dht-ping (dht peer)
  "True when PEER answers dht.ping with the random id we sent."
  (let* ((id (octets->uint (ironclad:random-data 7)))
         (answer (%dht-ask dht peer (tl-make "dht.ping" :random-id id))))
    (and answer (tl-is answer "dht.pong") (eql (tl-get answer :random-id) id))))

(defun %dht-merge-nodes (dht nodes-obj)
  "Verify every dht.node of the decoded dht.nodes NODES-OBJ and remember the good ones; the count of new nodes."
  (let ((new 0))
    (when (tl-is nodes-obj "dht.nodes")
      (loop for node across (coerce (tl-get nodes-obj :nodes) 'vector)
            do (let ((peer (dht-verify-node node)))
                 (when (and peer (%dht-add-peer dht peer)) (incf new)))))
    new))

(defun %dht-nearest (dht key-id &optional (count +dht-k+))
  "The COUNT known nodes nearest to KEY-ID that have not failed twice in a row."
  (let ((all (sb-thread:with-mutex ((dht-lock dht))
               (loop for p being the hash-values of (dht-peers dht) when (< (dht-peer-failures p) 2) collect p))))
    (let ((sorted (sort (mapcar (lambda (p) (cons (dht-distance (dht-peer-short-id p) key-id) p)) all) #'< :key #'car)))
      (mapcar #'cdr (subseq sorted 0 (min count (length sorted)))))))

(defun %dht-search (dht key-id query-fn &key (max-rounds 24))
  "Kademlia on KEY-ID: QUERY-FN (peer) -> (VALUES RESULT DONE) is called for the A nearest not yet answered of the K nearest nodes at a
time, in parallel (a node that did not answer is tried once more); it merges the nodes an answer names itself and returns a second
value T to end the search with RESULT.  Returns (VALUES RESULT CLOSEST-PEERS)."
  (let ((attempts (make-hash-table :test 'equalp)))
    (dotimes (round max-rounds)
      (let ((todo (remove-if-not (lambda (p)
                                   (let ((n (gethash (dht-peer-short-id p) attempts 0)))
                                     (or (zerop n) (and (< n 2) (plusp (dht-peer-failures p))))))
                                 (%dht-nearest dht key-id))))
        (when (null todo) (return))
        (let* ((batch (subseq todo 0 (min +dht-a+ (length todo))))
               (threads (mapcar (lambda (peer)
                                  (incf (gethash (dht-peer-short-id peer) attempts 0))
                                  (sb-thread:make-thread (lambda () (multiple-value-list (funcall query-fn peer)))
                                                         :name "dht-query"))
                                batch)))
          (dolist (thread threads)
            (destructuring-bind (&optional result done) (sb-thread:join-thread thread :default nil)
              (when done (return-from %dht-search (values result (%dht-nearest dht key-id)))))))))
    (values nil (%dht-nearest dht key-id))))

(defun dht-find-nodes (dht key-id)
  "The nodes nearest to KEY-ID the network knows, as far as the search gets: a list of DHT-PEERs, nearest first."
  (nth-value 1 (%dht-search dht key-id
                            (lambda (peer)
                              (%dht-merge-nodes dht (%dht-ask dht peer (tl-make "dht.findNode" :key (coerce key-id 'tl-octets) :k +dht-k+)))
                              nil))))

(defun dht-find-value (dht key-id)
  "The verified value stored under KEY-ID: (VALUES VALUE-OCTETS PUBLIC-KEY), or NIL when no node has it."
  (let ((found (%dht-search dht key-id
                            (lambda (peer)
                              (let ((answer (%dht-ask dht peer (tl-make "dht.findValue" :key (coerce key-id 'tl-octets) :k +dht-k+))))
                                (cond ((tl-is answer "dht.valueFound")
                                       (multiple-value-bind (data public) (dht-verify-value (tl-get answer :value) key-id)
                                         (if data (values (list data public) t) nil)))
                                      ((tl-is answer "dht.valueNotFound")
                                       (%dht-merge-nodes dht (tl-get answer :nodes))
                                       nil)
                                      (t nil)))))))
    (when found (values (first found) (second found)))))

(defun dht-find-address (dht short-id)
  "The ADNL address record of the node with SHORT-ID: (VALUES ADDRESS-LIST PUBLIC-KEY) from the DHT, verified, or NIL."
  (multiple-value-bind (data public) (dht-find-value dht (dht-key-id short-id))
    (when (and data (equalp (adnl-short-id public) (as-octets short-id)))
      (let ((list (ignore-errors (tl-decode data))))
        (when (tl-is list "adnl.addressList") (values list public))))))

;;; --- the candidate cache -------------------------------------------------------------------------------------------------------------

(defun dht-save-cache (dht path)
  "Write the nodes that answered to PATH (one line each: public key hex, host, port), through a temporary file."
  (let ((tmp (format nil "~A.tmp" path)))
    (with-open-file (out tmp :direction :output :if-exists :supersede)
      (loop for p being the hash-values of (dht-peers dht)
            when (plusp (dht-peer-answers p))
              do (format out "~A ~A ~D~%" (octets->hex (dht-peer-public p)) (dht-peer-host p) (dht-peer-port p))))
    (rename-file tmp path)
    path))

(defun dht-load-cache (dht path)
  "Remember the nodes PATH lists (nothing when it is missing or has bad lines); the number added."
  (let ((added 0))
    (when (probe-file path)
      (with-open-file (in path)
        (loop for line = (read-line in nil) while line
              do (ignore-errors
                  (destructuring-bind (hex host port) (split-sequence-spaces line)
                    (let ((public (hex->octets hex)))
                      (when (and (= 32 (length public))
                                 (%dht-add-peer dht (make-dht-peer :public public :short-id (adnl-short-id public)
                                                                   :host host :port (parse-integer port))))
                        (incf added))))))))
    added))

(defun split-sequence-spaces (line)
  "The space separated words of LINE."
  (let ((words '()) (start nil))
    (loop for i from 0 to (length line)
          do (let ((space (or (= i (length line)) (char= (char line i) #\Space))))
               (cond ((and space start) (push (subseq line start i) words) (setf start nil))
                     ((and (not space) (not start)) (setf start i)))))
    (nreverse words)))
