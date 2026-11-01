;;;; fake-network.lisp -- the Fake Chain as a network that accepts typed Lite API commands.
;;;;
;;;; A test (or a strategy test) that wants a network calls WITH-FAKE-NETWORK: it gets a FAKE-NETWORK, i.e. a running
;;;; fakechain (the emulator-backed liteserver on a virtual clock) and a verifying lite client connected to it, and talks to
;;;; it ONLY through typed lite API objects (FNET-EXECUTE = LITE-EXECUTE on that client: liteServer.* in, verified liteServer.*
;;;; answers out).  No ADNL, proxy, global config or block id appears in the test.  Time passes only when the test says so
;;;; (FNET-ADVANCE).

(in-package :cl-ton/test)

(defstruct (fake-network (:conc-name fnet-) (:copier nil))
  chain                                 ; the fakechain
  client)                               ; the verifying lite client on it

(defun call-with-fake-network (fn &key (blocks 1))
  "Start a fakechain, seal BLOCKS blocks, connect a lite client to it and call FN with the FAKE-NETWORK; everything is
closed when FN returns or signals."
  (let ((fc (cl-ton::start-fakechain)) client)
    (unwind-protect
         (progn
           (cl-ton::fakechain-advance fc blocks)
           (setf client (cl-ton::open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc)
                                                  (cl-ton::keypair-public (cl-ton::fakechain-keypair fc))
                                                  (%zero-block-id fc)))
           (unless (%lite-wait-ready client) (cl-ton::ton-error "the fake network's lite client did not come up"))
           (funcall fn (make-fake-network :chain fc :client client)))
      (ignore-errors (when client (cl-ton::close-lite-client client)))
      (cl-ton::stop-fakechain fc))))

(defmacro with-fake-network ((var &key (blocks 1)) &body body)
  `(call-with-fake-network (lambda (,var) ,@body) :blocks ,blocks))

(defun fnet-execute (net request)
  "Run the typed lite API function object REQUEST on NET: (VALUES typed-answer proof)."
  (cl-ton:lite-execute (fnet-client net) request))

(defun fnet-advance (net &optional (blocks 1))
  "Seal BLOCKS more blocks (the virtual clock moves); returns the head seqno."
  (cl-ton::fakechain-advance (fnet-chain net) blocks))

(defun fnet-fund-wallet (net &key (balance (nano 10)))
  "Deploy a funded wallet v5r1 in NET (the scenario key) and return it."
  (%seed-wallet (fnet-chain net) :balance balance))

(defun fnet-send (net message)
  "Send the external message cell MESSAGE with the typed liteServer.sendMessage; returns the typed liteServer.sendMsgStatus."
  (values (fnet-execute net (cl-ton::tl-make "liteServer.sendMessage" :body (cl-ton:serialize-boc message)))))

(defun fnet-account (net address)
  "The typed, verified liteServer.accountState of ADDRESS at the head the client proved."
  (values (fnet-execute net (cl-ton::tl-make "liteServer.getAccountState" :id (cl-ton::lite-sync (fnet-client net))
                                                                           :account (%lite-account-id address)))))

(defun fnet-balance (net address)
  "The balance of ADDRESS in nanotons out of the verified account state (0 for an absent account)."
  (let ((state (cl-ton::tl-get (fnet-account net address) :state)))
    (if (zerop (length state))
        0
        (or (getf (cl-ton::parse-account (first (cl-ton::parse-boc state))) :balance) 0))))

(defun test-fake-network ()
  (format t "fake network: a typed-Lite-API network for strategy tests~%")
  (if (not (%libs-available-p))
      (skip-missing "the fake network (emulator shared library)")
      (let ((to (fake-address #x77)))
        (with-fake-network (net :blocks 2)
          (let* ((w (fnet-fund-wallet net :balance (nano 5)))
                 (addr (cl-ton:wallet-address w)))
            (fnet-advance net 2)
            (check "fake network: a funded wallet is visible through the typed liteServer.getAccountState"
                   (= (nano 5) (fnet-balance net addr)))
            (check "fake network: an unknown account has balance 0"
                   (zerop (fnet-balance net to)))
            (let ((status (fnet-send net (%transfer w 0 to (nano 1)))))
              (check "fake network: a typed send is accepted into the pool"
                     (and (cl-ton::tl-is status "liteServer.sendMsgStatus") (= 1 (cl-ton::tl-get status :status)))))
            (check "fake network: nothing happens before a block is sealed" (zerop (fnet-balance net to)))
            (fnet-advance net 2)
            (check "fake network: after blocks the transfer has executed (typed read)"
                   (plusp (fnet-balance net to)))
            (check "fake network: the sender paid value plus fees"
                   (< (fnet-balance net addr) (- (nano 5) (nano 1)))))))))

(defun test-lite-api ()
  (format t "lite API: typed liteServer objects in, verified liteServer answers out~%")
  (if (not (%libs-available-p))
      (skip-missing "the typed lite API (emulator shared library)")
      (with-fake-network (net :blocks 3)
        (let* ((w (fnet-fund-wallet net :balance (nano 5)))
               (addr (cl-ton:wallet-address w))
               (to (fake-address #x78))
               (client (fnet-client net)))
          (fnet-advance net 2)
          ;; head, time, version
          (let ((info (fnet-execute net (cl-ton::tl-make "liteServer.getMasterchainInfo"))))
            (check "lite API getMasterchainInfo: the head the client proved"
                   (and (cl-ton::tl-is info "liteServer.masterchainInfo")
                        (= (cl-ton::tl-get (cl-ton::tl-get info :last) :seqno) (cl-ton::tl-get (cl-ton::lite-sync client) :seqno)))))
          (let ((ext (fnet-execute net (cl-ton::tl-make "liteServer.getMasterchainInfoExt" :mode 0))))
            (check "lite API getMasterchainInfoExt: proved head and its generation time"
                   (and (cl-ton::tl-is ext "liteServer.masterchainInfoExt") (plusp (cl-ton::tl-get ext :last-utime))
                        (= (cl-ton::tl-get (cl-ton::tl-get ext :last) :seqno) (cl-ton::tl-get (cl-ton::lite-sync client) :seqno)))))
          (check "lite API getTime and getVersion: the server's own answers, no proof"
                 (multiple-value-bind (time p1) (fnet-execute net (cl-ton::tl-make "liteServer.getTime"))
                   (multiple-value-bind (version p2) (fnet-execute net (cl-ton::tl-make "liteServer.getVersion"))
                     (and (cl-ton::tl-is time "liteServer.currentTime") (cl-ton::tl-is version "liteServer.version")
                          (null p1) (null p2)))))
          ;; accounts
          (multiple-value-bind (answer proof)
              (fnet-execute net (cl-ton::tl-make "liteServer.getAccountState" :id (cl-ton::lite-sync client) :account (%lite-account-id addr)))
            (check "lite API getAccountState: the verified answer and its account-state proof"
                   (and (cl-ton::tl-is answer "liteServer.accountState") (cl-ton::tl-is proof "clton.proofAccountState")
                        (= (fnet-balance net addr) (nano 5)))))
          (check "lite API getAccountState: an account that does not exist has no state"
                 (zerop (fnet-balance net to)))
          (check "lite API getAccountState: a block that is not of the chain is refused"
                 (handler-case
                     (progn (fnet-execute net (cl-ton::tl-make "liteServer.getAccountState"
                                                            :id (cl-ton::tl-block-id-ext :workchain -1 :seqno 2
                                                                                         :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 5)
                                                                                         :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 6))
                                                            :account (%lite-account-id addr)))
                            nil)
                   (error () t)))
          ;; send, then see it execute
          (let ((boc (cl-ton:serialize-boc (%transfer w 0 to (nano 1)))))
            (check "lite API sendMessage: status 1 (pool acceptance)"
                   (= 1 (cl-ton::tl-get (fnet-execute net (cl-ton::tl-make "liteServer.sendMessage" :body boc)) :status))))
          (fnet-advance net 3)
          (check "lite API: the message sent through sendMessage executed"
                 (plusp (fnet-balance net to)))
          ;; transactions
          (let* ((head (cl-ton::lite-sync client))
                 (state (fnet-execute net (cl-ton::tl-make "liteServer.getAccountState" :id head :account (%lite-account-id addr))))
                 (answer nil) (proof nil))
            (declare (ignore state))
            (multiple-value-setq (answer proof)
              (let* ((r (cl-ton::lite-account-state client addr)))
                (fnet-execute net (cl-ton::tl-make "liteServer.getTransactions" :count 10 :account (%lite-account-id addr)
                                                                             :lt (getf r :last-trans-lt) :hash (getf r :last-trans-hash)))))
            (check "lite API getTransactions: the verified list, with the transactions proof"
                   (and (cl-ton::tl-is answer "liteServer.transactionList") (cl-ton::tl-is proof "clton.proofTransactions")
                        (>= (length (cl-ton::tl-get answer :ids)) 1)
                        (= (length (cl-ton::tl-get answer :ids)) (length (cl-ton::parse-boc (cl-ton::tl-get answer :transactions)))))))
          ;; a getter: the wallet's seqno, run by the client's emulator on the proved state
          (multiple-value-bind (answer proof)
              (fnet-execute net (cl-ton::tl-make "liteServer.runSmcMethod" :mode 4 :id (cl-ton::lite-sync client) :account (%lite-account-id addr)
                                                                        :method-id (cl-ton::method-id "seqno")
                                                                        :params (cl-ton:serialize-boc (list (cl-ton::serialize-vm-stack nil)) :has-crc32c nil)))
            (check "lite API runSmcMethod: the proved getter result, with its run proof"
                   (and (cl-ton::tl-is answer "liteServer.runMethodResult") (cl-ton::tl-is proof "clton.proofRunMethod")
                        (zerop (cl-ton::tl-get answer :exit-code))
                        (equal (cl-ton::parse-vm-stack (first (cl-ton::parse-boc (cl-ton::tl-get answer :result))))
                               (cl-ton::lite-backend-run-get-method client addr "seqno")))))
          ;; blocks
          (let* ((shard (- (expt 2 63)))
                 (header (fnet-execute net (cl-ton::tl-make "liteServer.lookupBlock" :mode 1
                                                         :id (cl-ton::tl-make "tonNode.blockId" :workchain 0 :shard shard :seqno 2)))))
            (check "lite API lookupBlock by seqno: the verified header of the block"
                   (and (cl-ton::tl-is header "liteServer.blockHeader") (= 2 (cl-ton::tl-get (cl-ton::tl-get header :id) :seqno))))
            (check "lite API getBlockHeader: the same header for the id lookupBlock found"
                   (equalp (cl-ton::tl-get header :header-proof)
                           (cl-ton::tl-get (fnet-execute net (cl-ton::tl-make "liteServer.getBlockHeader" :id (cl-ton::tl-get header :id) :mode 0))
                                           :header-proof))))
          (multiple-value-bind (answer proof)
              (fnet-execute net (cl-ton::tl-make "liteServer.getAllShardsInfo" :id (cl-ton::lite-sync client)))
            (check "lite API getAllShardsInfo: the verified shards, with their proof"
                   (and (cl-ton::tl-is answer "liteServer.allShardsInfo") (cl-ton::tl-is proof "clton.proofAllShards"))))
          (multiple-value-bind (answer proof)
              (fnet-execute net (cl-ton::tl-make "liteServer.getConfigAll" :mode 0 :id (cl-ton::lite-sync client)))
            (check "lite API getConfigAll: the verified configuration, with its proof"
                   (and (cl-ton::tl-is answer "liteServer.configInfo") (cl-ton::tl-is proof "clton.proofConfig"))))
          (check "lite API: a function the client does not run is refused"
                 (handler-case (progn (fnet-execute net (cl-ton::tl-make "liteServer.getState"
                                                                      :id (cl-ton::lite-sync client)))
                                      nil)
                   (cl-ton:ton-error () t)))
          (check "lite API: the supported list names the functions"
                 (every (lambda (n) (member n (cl-ton:lite-execute-supported) :test #'string=))
                        '("liteServer.getAccountState" "liteServer.getTransactions" "liteServer.runSmcMethod"
                          "liteServer.sendMessage" "liteServer.getBlockHeader" "liteServer.lookupBlock")))))))

(defun test-lite-api-more ()
  (format t "lite API: block transactions, config parameters, libraries, shard info, block proofs, the freshness floor~%")
  (if (not (%libs-available-p))
      (skip-missing "the typed Lite API, second part (emulator shared library)")
      (with-fake-network (net :blocks 3)
        (let* ((w (fnet-fund-wallet net :balance (nano 5)))
               (to (fake-address #x79))
               (client (fnet-client net))
               (shard (- (expt 2 63)))
               (lib (cl-ton:end-cell (cl-ton:store-uint (cl-ton:begin-cell) 4242 32)))
               (lib-hash (cl-ton::hex->octets (cl-ton::fakechain-add-library (fnet-chain net) lib))))
          (fnet-send net (%transfer w 0 to (nano 1)))
          (fnet-advance net 4)
          ;; the block that holds the transfer
          (let ((found nil))
            (loop for seqno from 1 to (cl-ton::tl-get (cl-ton::lite-sync client) :seqno)
                  until found
                  do (let* ((header (fnet-execute net (cl-ton::tl-make "liteServer.lookupBlock" :mode 1
                                                                       :id (cl-ton::tl-make "tonNode.blockId" :workchain 0 :shard shard :seqno seqno))))
                            (id (cl-ton::tl-get header :id)))
                       (multiple-value-bind (answer proof)
                           (fnet-execute net (cl-ton::tl-make "liteServer.listBlockTransactions" :id id :mode 7 :count 40))
                         (when (plusp (length (cl-ton::tl-get answer :ids)))
                           (setf found (list id answer proof))))))
            (check "lite API listBlockTransactions: the block with the transfer lists its transactions, proved"
                   (and found
                        (cl-ton::tl-is (second found) "liteServer.blockTransactions")
                        (cl-ton::tl-is (third found) "clton.proofBlockTransactions")
                        (cl-ton:verify-proof (third found))
                        (not (cl-ton::tl-get (second found) :incomplete))))
            (when found
              (let* ((id (first found))
                     (tid (first (coerce (cl-ton::tl-get (second found) :ids) 'list)))
                     (info (fnet-execute net (cl-ton::tl-make "liteServer.getOneTransaction" :id id
                                                              :account (cl-ton::tl-make "liteServer.accountId" :workchain 0
                                                                                                               :id (cl-ton::tl-get tid :account))
                                                              :lt (cl-ton::tl-get tid :lt))))
                     (roots (cl-ton::parse-boc (cl-ton::tl-get info :transaction)))
                     (ext (fnet-execute net (cl-ton::tl-make "liteServer.listBlockTransactionsExt" :id id :mode 7 :count 40))))
                (check "lite API getOneTransaction: the transaction the block lists, proved to be in it"
                       (and (cl-ton::tl-is info "liteServer.transactionInfo") (= 1 (length roots))
                            (equalp (cl-ton::node-hash (first roots)) (cl-ton::tl-get tid :hash))))
                (check "lite API getOneTransaction: a transaction that is not the block's no longer verifies"
                       (handler-case
                           (progn (cl-ton::verify-one-transaction
                                   (cl-ton::tl-make "liteServer.transactionInfo" :id id :proof (cl-ton::tl-get info :proof)
                                                    :transaction (cl-ton:serialize-boc
                                                                  (list (cl-ton:end-cell (cl-ton:store-uint (cl-ton:begin-cell) 1 8)))))
                                   id (cl-ton::tl-get tid :account) (cl-ton::tl-get tid :lt))
                                  nil)
                         (error () t)))
                (check "lite API listBlockTransactionsExt: the same transactions in full, each bound to the block"
                       (and (cl-ton::tl-is ext "liteServer.blockTransactionsExt")
                            (= (length (cl-ton::tl-get (second found) :ids))
                               (length (cl-ton::parse-boc (cl-ton::tl-get ext :transactions))))))
                (check "lite API listBlockTransactionsExt: a served transaction that was altered no longer verifies"
                       (handler-case
                           (progn (cl-ton::verify-block-transactions-ext
                                   (cl-ton::tl-make "liteServer.blockTransactionsExt" :id id :req-count 40 :incomplete nil
                                                    :transactions (cl-ton:serialize-boc
                                                                   (list (cl-ton:end-cell (cl-ton:store-uint (cl-ton:begin-cell) 1 8))))
                                                    :proof (cl-ton::tl-get ext :proof))
                                   id :count 40)
                                  nil)
                         (error () t))))))
          ;; whole blocks
          (dolist (wc '(-1 0))
            (let* ((id (cl-ton::tl-get (fnet-execute net (cl-ton::tl-make "liteServer.lookupBlock" :mode 1
                                                                           :id (cl-ton::tl-make "tonNode.blockId" :workchain wc :shard shard :seqno 2)))
                                       :id))
                   (answer (fnet-execute net (cl-ton::tl-make "liteServer.getBlock" :id id))))
              (check (format nil "lite API getBlock (workchain ~D): the block, hashing to the id's file and root hash" wc)
                     (and (cl-ton::tl-is answer "liteServer.blockData")
                          (equalp (cl-ton::sha256 (cl-ton::tl-get answer :data)) (cl-ton::tl-get id :file-hash))))
              (check (format nil "lite API getBlock (workchain ~D): altered block data no longer verifies" wc)
                     (handler-case
                         (progn (cl-ton::verify-block-data
                                 (cl-ton::tl-make "liteServer.blockData" :id id
                                                  :data (%flipped-copy (cl-ton::tl-get answer :data)
                                                                       (floor (length (cl-ton::tl-get answer :data)) 2)))
                                 id)
                                nil)
                       (error () t)))))
          ;; config parameters
          (let* ((trusted (cl-ton::lite-sync client))
                 (answer (fnet-execute net (cl-ton::tl-make "liteServer.getConfigParams" :mode 0 :id trusted
                                                            :param-list (vector 34))))
                 (param (cdr (assoc 34 (getf (cl-ton::verify-config-info answer trusted :params '(34)) :params)))))
            (check "lite API getConfigParams: the revealed parameter is the one of the whole proved configuration"
                   (and (cl-ton::tl-is answer "liteServer.configInfo") param
                        (equal (cl-ton::cell-hash-hex param)
                               (cl-ton::cell-hash-hex (cl-ton::config-param (cl-ton::lite-backend-config-cell client) 34))))))
          ;; libraries
          (let ((answer (fnet-execute net (cl-ton::tl-make "liteServer.getLibraries" :library-list (list lib-hash))))
                (absent (fnet-execute net (cl-ton::tl-make "liteServer.getLibraries"
                                                           :library-list (list (make-array 32 :element-type '(unsigned-byte 8) :initial-element 9))))))
            (check "lite API getLibraries: a published library comes back proved, an unknown one is left out"
                   (and (= 1 (length (cl-ton::tl-get answer :result)))
                        (equal (cl-ton::cell-hash-hex lib)
                               (cl-ton::cell-hash-hex (first (cl-ton::parse-boc (cl-ton::tl-get (first (cl-ton::tl-get answer :result)) :data)))))
                        (zerop (length (cl-ton::tl-get absent :result))))))
          (check "lite API getLibrariesWithProof: the same library with the state proof of the masterchain"
                 (let ((answer (fnet-execute net (cl-ton::tl-make "liteServer.getLibrariesWithProof" :id (cl-ton::lite-sync client) :mode 1
                                                                  :library-list (list lib-hash)))))
                   (and (cl-ton::tl-is answer "liteServer.libraryResultWithProof")
                        (= 1 (length (cl-ton::tl-get answer :result))))))
          ;; shard info and shard block proof
          (let* ((info (fnet-execute net (cl-ton::tl-make "liteServer.getShardInfo" :id (cl-ton::lite-sync client)
                                                          :workchain 0 :shard shard :exact t)))
                 (found (cl-ton::lite-shard-info client 0 (ldb (byte 64 0) shard) :exact t)))
            (check "lite API getShardInfo: the shard block the masterchain names, as the client's own lookup finds"
                   (and (cl-ton::tl-is info "liteServer.shardInfo") (getf found :found)
                        (= (cl-ton::tl-get (cl-ton::tl-get info :shardblk) :seqno) (getf found :seqno))))
            (let ((proof (fnet-execute net (cl-ton::tl-make "liteServer.getShardBlockProof" :id (cl-ton::tl-get info :shardblk)))))
              (check "lite API getShardBlockProof: the links from a masterchain block to that shard block"
                     (and (cl-ton::tl-is proof "liteServer.shardBlockProof")
                          (= -1 (cl-ton::tl-get (cl-ton::tl-get proof :masterchain-id) :workchain))))))
          ;; block proof from an old masterchain block to the head
          (let* ((old (cl-ton::tl-get (fnet-execute net (cl-ton::tl-make "liteServer.lookupBlock" :mode 1
                                                                         :id (cl-ton::tl-make "tonNode.blockId" :workchain -1 :shard shard :seqno 1)))
                                      :id))
                 (head (cl-ton::lite-sync client))
                 (proof (fnet-execute net (cl-ton::tl-make "liteServer.getBlockProof" :mode 1 :known-block old :target-block head))))
            (check "lite API getBlockProof: the verified chain of links from an older block to the head"
                   (and (cl-ton::tl-is proof "liteServer.partialBlockProof") (cl-ton::tl-get proof :complete))))
          ;; the freshness floor
          (let ((before (cl-ton::tl-get (cl-ton::lite-sync client) :seqno)))
            (fnet-advance net 2)
            (check "lite API: with a freshness floor the request runs on a head at or above it"
                   (>= (cl-ton::tl-get (cl-ton::tl-get (cl-ton:lite-execute client (cl-ton::tl-make "liteServer.getMasterchainInfo")
                                                                             :min-seqno (+ before 2))
                                                       :last)
                                       :seqno)
                       (+ before 2))))))))

(defun test-lite-api-masterchain ()
  (format t "lite API: masterchain accounts, transactions and messages across the workchains~%")
  (if (not (%libs-available-p))
      (skip-missing "the masterchain on the fake network (emulator shared library)")
      (with-fake-network (net :blocks 2)
        (let* ((shard (- (expt 2 63)))
               (client (fnet-client net))
               (w0 (fnet-fund-wallet net :balance (nano 10)))
               (mcw (cl-ton::make-wallet-v5r1 *scenario-keypair* :workchain -1))
               (mc-addr (cl-ton:wallet-address mcw))
               (to0 (fake-address #x7b))
               (mc-fresh (cl-ton::make-address :workchain -1 :hash (cl-ton::address-hash (fake-address #x7a)))))
          (cl-ton::fakechain-set-account (fnet-chain net) mc-addr :state-init (cl-ton::wallet-state-init mcw) :balance (nano 20))
          (fnet-advance net 2)
          (check "masterchain: a funded masterchain wallet is read, proved in the masterchain block itself"
                 (= (nano 20) (fnet-balance net mc-addr)))
          (check "masterchain: its getter runs on the proved state (wallet seqno 0)"
                 (let ((answer (fnet-execute net (cl-ton::tl-make "liteServer.runSmcMethod" :mode 4 :id (cl-ton::lite-sync client)
                                                                  :account (%lite-account-id mc-addr) :method-id (cl-ton::method-id "seqno")
                                                                  :params (cl-ton:serialize-boc (list (cl-ton::serialize-vm-stack nil)) :has-crc32c nil)))))
                   (and (zerop (cl-ton::tl-get answer :exit-code))
                        (equal (cl-ton::parse-vm-stack (first (cl-ton::parse-boc (cl-ton::tl-get answer :result))))
                               (cl-ton::lite-backend-run-get-method client mc-addr "seqno")))))
          ;; masterchain -> workchain 0
          (fnet-send net (%transfer mcw 0 to0 (nano 1)))
          ;; workchain 0 -> masterchain (an address that does not exist yet: it gets the value)
          (fnet-send net (%transfer w0 0 mc-fresh (nano 2)))
          (fnet-advance net 4)
          (check "masterchain: a message from the masterchain wallet reached workchain 0"
                 (plusp (fnet-balance net to0)))
          (check "masterchain: a message from workchain 0 reached a masterchain address"
                 (plusp (fnet-balance net mc-fresh)))
          (check "masterchain: the wallet paid the transfer and fees"
                 (< (fnet-balance net mc-addr) (- (nano 20) (nano 1))))
          ;; its transactions
          (let* ((r (cl-ton::lite-account-state client mc-addr))
                 (answer (fnet-execute net (cl-ton::tl-make "liteServer.getTransactions" :count 10 :account (%lite-account-id mc-addr)
                                                            :lt (getf r :last-trans-lt) :hash (getf r :last-trans-hash)))))
            (check "masterchain: the wallet's transactions are listed, each chained to the one before"
                   (and (>= (length (cl-ton::tl-get answer :ids)) 1)
                        (= -1 (cl-ton::tl-get (first (coerce (cl-ton::tl-get answer :ids) 'list)) :workchain)))))
          ;; the masterchain block that holds them
          (let ((found nil))
            (loop for seqno from 1 to (cl-ton::tl-get (cl-ton::lite-sync client) :seqno)
                  until found
                  do (let ((id (cl-ton::tl-get (fnet-execute net (cl-ton::tl-make "liteServer.lookupBlock" :mode 1
                                                                                  :id (cl-ton::tl-make "tonNode.blockId" :workchain -1 :shard shard :seqno seqno)))
                                               :id)))
                       (multiple-value-bind (answer proof)
                           (fnet-execute net (cl-ton::tl-make "liteServer.listBlockTransactions" :id id :mode 7 :count 40))
                         (when (plusp (length (cl-ton::tl-get answer :ids)))
                           (setf found (list id answer proof))))))
            (check "masterchain: a masterchain block lists its transactions, proved"
                   (and found (cl-ton:verify-proof (third found))))
            (when found
              (let* ((id (first found))
                     (tid (first (coerce (cl-ton::tl-get (second found) :ids) 'list)))
                     (info (fnet-execute net (cl-ton::tl-make "liteServer.getOneTransaction" :id id
                                                              :account (cl-ton::tl-make "liteServer.accountId" :workchain -1
                                                                                                               :id (cl-ton::tl-get tid :account))
                                                              :lt (cl-ton::tl-get tid :lt)))))
                (check "masterchain: getOneTransaction proves a transaction inside a masterchain block"
                       (equalp (cl-ton::node-hash (first (cl-ton::parse-boc (cl-ton::tl-get info :transaction))))
                               (cl-ton::tl-get tid :hash))))))))))

(defun fnet-external-outs (net)
  "The outgoing external messages (contract events) the fake chain processed so far: plists (:MESSAGE :SRC :UTIME)."
  (cl-ton::fakechain-external-outs (fnet-chain net)))

(defun %external-out-message (src-hash lt)
  "An ext_out_msg_info message from the workchain-0 account SRC-HASH with an empty inline body."
  (let ((b (cl-ton:begin-cell)))
    (setf b (cl-ton:store-uint b #b11 2))                       ; ext_out_msg_info$11
    (setf b (cl-ton:store-uint b #b100 3))                      ; src: addr_std$10, no anycast
    (setf b (cl-ton:store-uint b 0 8))                          ; workchain 0
    (setf b (cl-ton:store-bytes b src-hash))
    (setf b (cl-ton:store-uint b 0 2))                          ; dest: addr_none
    (setf b (cl-ton:store-uint b lt 64))                        ; created_lt
    (setf b (cl-ton:store-uint b 7 32))                         ; created_at
    (setf b (cl-ton:store-uint b 0 2))                          ; no init, body inline
    (cl-ton:end-cell b)))

(defun test-fake-external-out ()
  (format t "fake network: outgoing external messages are recorded, not delivered~%")
  (with-fake-network (net :blocks 1)
    (let* ((src (fake-address #x30))
           (w (fnet-fund-wallet net :balance (nano 5))))
      (check "external-out: nothing recorded before any is processed"
             (null (fnet-external-outs net)))
      (%fc-enqueue (fnet-chain net) (%external-out-message (cl-ton::address-hash src) 5))
      (fnet-advance net 2)
      (let ((events (fnet-external-outs net)))
        (check "external-out: one event, from the emitting account, at the chain time"
               (and (= 1 (length events))
                    (cl-ton::address-equal (getf (first events) :src) src)
                    (plusp (getf (first events) :utime))
                    (cl-ton::cell-p (getf (first events) :message)))))
      (check "external-out: it changed no account (the funded wallet is as it was)"
             (= (nano 5) (fnet-balance net (cl-ton:wallet-address w)))))))
