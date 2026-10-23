;;;; lite.lisp -- the verifying liteserver client against the fakechain, over a real ADNL-ext session

(in-package :cl-ton/test)

(defun %lite-wait-ready (client)
  (loop repeat 100 until (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl client)) do (sleep 0.1))
  (cl-ton::adnl-ext-client-ready-p (cl-ton::lite-client-adnl client)))

(defvar *pmap-test-special* :global)
(pushnew '*pmap-test-special* cl-ton::*pmap-conveyed*)

(defun test-pmap-conveys ()
  (format t "pmap: the dynamic settings that matter reach its worker threads~%")
  (check "a bound conveyed special is seen by every worker (a new thread sees the global value otherwise)"
         (equal '(:bound :bound :bound :bound)
                (let ((*pmap-test-special* :bound))
                  (cl-ton:pmap (lambda (x) (declare (ignore x)) *pmap-test-special*) '(1 2 3 4) :threads 4))))
  (check "the block the getters are pinned to is one of them"
         (equal '(:pinned :pinned :pinned)
                (let ((cl-ton:*get-method-block* :pinned))
                  (cl-ton:pmap (lambda (x) (declare (ignore x)) cl-ton:*get-method-block*) '(1 2 3) :threads 3))))
  (check "...and outside the binding the workers see the global value again"
         (equal '(:global :global)
                (cl-ton:pmap (lambda (x) (declare (ignore x)) *pmap-test-special*) '(1 2) :threads 2)))
  (check "the order of the results is the order of the list"
         (equal '(2 4 6 8 10) (cl-ton:pmap (lambda (x) (* 2 x)) '(1 2 3 4 5) :threads 3))))

(defun test-lite-client ()
  (format t "lite client: sync, account state, transactions, getter and send over ADNL-ext~%")
  (if (not (%libs-available-p))
      (skip-missing "lite client (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (cl-ton:wallet-address w))
                (dest (fake-address #x66))
                (zero (%zero-block-id fc))
                (public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc))))
           (dotimes (seqno 3)
             (%fc-enqueue fc (%transfer w seqno dest (cl-ton::nano 1/10)))
             (cl-ton::fakechain-advance fc 2))
           (let ((client (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public zero)))
             (unwind-protect
                  (progn
                    (check "the client connects" (%lite-wait-ready client))
                    (let ((head (cl-ton:lite-sync client)))
                      (check "sync proves the head the fakechain has"
                             (and (= (cl-ton::tl-get head :seqno) (cl-ton::fc-head-seqno fc))
                                  (plusp (cl-ton::tl-get head :seqno))
                                  (eq head (cl-ton:lite-client-trusted client)))))
                    (let ((state (cl-ton:lite-account-state client addr)))
                      (check "the wallet's state is proved: it exists with a last transaction"
                             (and (getf state :exists) (plusp (getf state :last-trans-lt)))))
                    (let ((r (cl-ton:lite-transactions client addr :count 20)))
                      (check "its three transactions come back chained to the proved last one"
                             (and (= 3 (length (getf r :transactions))) (getf r :complete))))
                    (check "a server that does not have the block yet (error 651) is asked again until it has it"
                           (progn
                             (setf (cl-ton::fakechain-lagging-p fc) t)
                             (sb-thread:make-thread (lambda () (sleep 1.5) (setf (cl-ton::fakechain-lagging-p fc) nil)))
                             (let ((state (cl-ton:lite-account-state client addr)))
                               (and (getf state :exists) (plusp (getf state :last-trans-lt))))))
                    (check "...and one that never has it ends in that error, not in a hang"
                           (let ((head (cl-ton:lite-sync client)))
                             (setf (cl-ton::fakechain-lagging-p fc) t)
                             (unwind-protect
                                  (handler-case (progn (cl-ton:lite-call client (cl-ton::tl-make "liteServer.getAccountState"
                                                                                                  :id head
                                                                                                  :account (cl-ton::%lite-account-id addr))
                                                                         :deadline 2)
                                                       nil)
                                    (cl-ton:lite-error (e) (eql 651 (cl-ton::lite-error-code e))))
                               (setf (cl-ton::fakechain-lagging-p fc) nil))))
                    (check "a getter on the proved state: seqno is the number of transfers sent"
                           (equal '(3) (cl-ton:lite-run-get-method client addr "seqno" '())))
                    (check "the liteserver's own run of the getter (unproved runSmcMethod) gives the same stack and exit code"
                           (multiple-value-bind (items exit) (cl-ton:lite-server-get-method client addr "seqno" '())
                             (and (equal '(3) items) (eql 0 exit))))
                    (check "...for a numeric method id too, and for an account that is not there it is a liteserver error"
                           (and (equal '(3) (cl-ton:lite-server-get-method client addr (cl-ton::method-id "seqno") '()))
                                (handler-case (progn (cl-ton:lite-server-get-method client (fake-address #x99) "seqno" '()) nil)
                                  (cl-ton:lite-error (e) (eql 609 (cl-ton::lite-error-code e))))))
                    (check "an account that does not exist has no transactions"
                           (null (getf (cl-ton:lite-transactions client (fake-address #x99)) :transactions)))
                    (let* ((pinned (cl-ton:lite-sync client))
                           (message (%transfer w 3 dest (cl-ton::nano 1/10)))
                           (boc (cl-ton:serialize-boc message))
                           (hash (cl-ton:lite-send-message client boc)))
                      (check "a sent message returns its hash" (equalp hash (cl-ton:node-hash message)))
                      (cl-ton::fakechain-advance fc 2)
                      (check "...and the chain took it: the getter now says 4"
                             (equal '(4) (cl-ton:lite-run-get-method client addr "seqno" '())))
                      (check "a getter pinned to the block before reads THAT block: seqno 3, not 4"
                             (equal '(3) (cl-ton:lite-run-get-method client addr "seqno" '() :block pinned)))
                      (check "...and so does the backend's getter when *get-method-block* is bound (the observe mode's snapshot)"
                             (let ((cl-ton::*get-method-block* (cl-ton::lite-block-id->tlapi pinned)))
                               (equal '(3) (cl-ton::lite-backend-run-get-method client addr "seqno" '()))))
                      (check "the configuration of a pinned block is fetched once and kept"
                             (eq (cl-ton::lite-backend-config-cell client pinned) (cl-ton::lite-backend-config-cell client pinned)))
                      (check "...unbound, the backend reads the newest head again: 4"
                             (equal '(4) (cl-ton::lite-backend-run-get-method client addr "seqno" '())))
                      (check "...a pinned block is proved once (a second read does not ask for another proof)"
                             (= 1 (let ((n 0))
                                    (when (gethash (list (cl-ton::tl-get pinned :seqno) (cl-ton::tl-get pinned :root-hash))
                                                   (cl-ton::lite-client-proved client))
                                      (incf n))
                                    n)))
                      (check "a pinned block that is not of the trusted chain is refused"
                             (handler-case
                                 (progn (cl-ton:lite-run-get-method
                                         client addr "seqno" '()
                                         :block (cl-ton::tl-block-id-ext :workchain -1 :seqno (cl-ton::tl-get pinned :seqno)
                                                                         :root-hash (%flip-octet (cl-ton::tl-get pinned :root-hash) 0)
                                                                         :file-hash (cl-ton::tl-get pinned :file-hash)))
                                        nil)
                               ((or cl-ton:proof-error cl-ton:lite-error) () t))))
                    (check "a liteserver error is a LITE-ERROR, not a hang or a crash"
                           (handler-case
                               (progn (cl-ton:lite-call client (cl-ton::tl-make "liteServer.getBlockHeader"
                                                                                 :id (cl-ton::tl-block-id-ext :seqno 99999999)
                                                                                 :mode 0))
                                      nil)
                             (cl-ton:lite-error () t))))
               (cl-ton:close-lite-client client)))
           ;; a client whose anchor is not the chain's zero block cannot prove anything
           (let ((wrong (cl-ton::tl-block-id-ext :seqno 0 :root-hash (%flip-octet (cl-ton::fakechain-zero-root fc) 0)
                                                 :file-hash (cl-ton::fakechain-zero-file fc)))
                 (client nil))
             (setf client (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public wrong))
             (unwind-protect
                  (progn (%lite-wait-ready client)
                         (check "a client anchored at another block than the chain's proves nothing"
                                (handler-case (progn (cl-ton:lite-sync client) nil)
                                  (cl-ton:proof-error () t)
                                  (cl-ton:lite-error () t))))
               (cl-ton:close-lite-client client))))))))

;;; --- 3.3b: persisted trust state, reconnects, waiting for a block ------------------------------

(defun %lite-file-octets (path)
  (with-open-file (in path :element-type '(unsigned-byte 8))
    (let ((v (make-array (file-length in) :element-type '(unsigned-byte 8)))) (read-sequence v in) v)))

(defun %lite-put-octets (path octets &optional (mode #o600))
  (with-open-file (out path :element-type '(unsigned-byte 8) :if-exists :supersede :direction :output)
    (write-sequence octets out))
  (sb-posix:chmod (namestring path) mode))

(defun test-lite-commit-key ()
  (format t "lite client: key blocks proved on the way are kept~%")
  (let* ((dir (%tmpdir "lite-commit"))
         (path (format nil "~Astate/lite.state" dir))
         (id (lambda (seqno byte) (cl-ton::tl-block-id-ext :seqno seqno
                                                           :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element byte)
                                                           :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element (1+ byte)))))
         (anchor (funcall id 7 1))
         (client (cl-ton::%make-lite-client :anchor anchor :trusted anchor :key-block anchor :state-file path))
         (k1 (funcall id 500 3)) (k2 (funcall id 900 5))
         (h1 (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7))
         (h2 (make-array 32 :element-type '(unsigned-byte 8) :initial-element 8)))
    (cl-ton::%lite-commit-key client k1 h1)
    (check "a key block committed mid-sync becomes the client's key block and head"
           (and (cl-ton::%lite-same-block-p (cl-ton::lite-client-key-block client) k1)
                (cl-ton::%lite-same-block-p (cl-ton::lite-client-trusted client) k1)))
    (multiple-value-bind (k h) (cl-ton::%lite-load-state path anchor)
      (check "...and it is already in the state file, for the next attempt or run"
             (and k (cl-ton::%lite-same-block-p k k1) (equalp h h1))))
    (cl-ton::%lite-commit-key client k2 h2)
    (check "a later one replaces it"
           (multiple-value-bind (k h) (cl-ton::%lite-load-state path anchor)
             (and k (cl-ton::%lite-same-block-p k k2) (equalp h h2))))
    (cl-ton::%lite-commit-key client k1 h1)
    (check "an older one never moves it back"
           (and (cl-ton::%lite-same-block-p (cl-ton::lite-client-key-block client) k2)
                (equalp (cl-ton::lite-client-key-state-hash client) h2)))))

(defun test-lite-state-file ()
  (format t "lite client: the persisted trust state~%")
  (let* ((dir (%tmpdir "lite-state"))
         (path (format nil "~Astate/lite.state" dir))
         (anchor (cl-ton::tl-block-id-ext :seqno 7 :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 1)
                                          :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 2)))
         (key (cl-ton::tl-block-id-ext :seqno 900 :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 3)
                                       :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 4)))
         (shash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 5))
         (good (cl-ton::%lite-state-octets anchor key shash))
         (client (cl-ton::%make-lite-client :anchor anchor :trusted anchor :key-block key
                                            :key-state-hash shash :state-file path)))
    (cl-ton::%lite-save-state client)
    (check "a state file is written, privately (mode 600) in a directory created 700"
           (and (probe-file path)
                (= #o600 (logand #o777 (sb-posix:stat-mode (sb-posix:stat path))))
                (= #o700 (logand #o777 (sb-posix:stat-mode (sb-posix:stat (format nil "~Astate" dir)))))))
    (check "...and it is exactly the encoding the loader reads" (equalp good (%lite-file-octets path)))
    (multiple-value-bind (k h) (cl-ton::%lite-load-state path anchor)
      (check "it loads back: the same key block and state hash"
             (and k (cl-ton::%lite-same-block-p k key) (equalp h shash))))
    (check "a client with ANOTHER anchor ignores it"
           (null (cl-ton::%lite-load-state path (cl-ton::tl-block-id-ext :seqno 7 :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 9)))))
    (check "...and so does a client whose anchor is NEWER than the saved key block"
           (null (cl-ton::%lite-load-state path (cl-ton::tl-block-id-ext :seqno 901 :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 1)
                                                                          :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 2)))))
    ;; every single-octet corruption is refused (the checksum covers the body; the magic is checked)
    (let ((accepted 0))
      (dotimes (i (length good))
        (%lite-put-octets path (%flip-octet good i))
        (when (cl-ton::%lite-load-state path anchor) (incf accepted)))
      (check "no single-octet corruption of the file is accepted" (zerop accepted)))
    (check "a truncated file and an empty file are refused"
           (progn (%lite-put-octets path (subseq good 0 (- (length good) 5)))
                  (and (null (cl-ton::%lite-load-state path anchor))
                       (progn (%lite-put-octets path (subseq good 0 0)) (null (cl-ton::%lite-load-state path anchor))))))
    (%lite-put-octets path good #o666)
    (check "a file other users can write is refused" (null (cl-ton::%lite-load-state path anchor)))
    (%lite-put-octets path good #o600)
    (check "...and accepted again at mode 600" (and (cl-ton::%lite-load-state path anchor) t))
    (check "a missing file is no error" (null (cl-ton::%lite-load-state (format nil "~Anothing" dir) anchor)))
    ;; a key block that IS the anchor is stored without a state hash; with one it is refused
    (let ((at-anchor (cl-ton::%lite-state-octets anchor anchor nil)))
      (%lite-put-octets path at-anchor)
      (check "the anchor itself as the key block loads, with no state hash"
             (multiple-value-bind (k h) (cl-ton::%lite-load-state path anchor) (and k (null h))))
      (%lite-put-octets path (cl-ton::%lite-state-octets anchor anchor shash))
      (check "...but not with a state hash attached" (null (cl-ton::%lite-load-state path anchor))))
    (%lite-put-octets path (cl-ton::%lite-state-octets anchor key nil))
    (check "a later key block without a state hash loads as it is (real links carry none): the next start resumes there"
           (multiple-value-bind (k h) (cl-ton::%lite-load-state path anchor)
             (and k (null h) (eql (cl-ton::tl-get k :seqno) (cl-ton::tl-get key :seqno)))))
    (let ((other-wc (cl-ton::tl-block-id-ext :workchain 0 :seqno 900)))
      (%lite-put-octets path (cl-ton::%lite-state-octets anchor other-wc shash))
      (check "a key block of another chain (workchain 0) is refused" (null (cl-ton::%lite-load-state path anchor))))))

(defun test-lite-resilience ()
  (format t "lite client: persisted sync state, reconnect, waiting for a block~%")
  (if (not (%libs-available-p))
      (skip-missing "lite client resilience (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (cl-ton:wallet-address w))
                (zero (%zero-block-id fc))
                (public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                (path (format nil "~Astate/lite.state" (%tmpdir "lite-resil")))
                (port (cl-ton::fakechain-port fc)))
           (cl-ton::fakechain-advance fc 2)
           ;; 1. a client with a state file saves what it proved; the next one starts from it
           (let ((client (cl-ton:open-lite-client "127.0.0.1" port public zero :state-file path)))
             (unwind-protect
                  (progn (%lite-wait-ready client)
                         (check "no file at first: the client starts from its anchor"
                                (and (not (probe-file path)) (eq (cl-ton::lite-client-key-block client) zero)))
                         (cl-ton:lite-sync client))
               (cl-ton:close-lite-client client)))
           (let ((client (cl-ton:open-lite-client "127.0.0.1" port public zero :state-file path)))
             (unwind-protect
                  (progn (%lite-wait-ready client)
                         (check "a restarted client keeps working from the same trust"
                                (cl-ton::%lite-same-block-p (cl-ton::lite-client-key-block client) zero))
                         (check "...and it still proves state (the file never replaces a proof)"
                                (getf (cl-ton:lite-account-state client addr) :exists)))
               (cl-ton:close-lite-client client)))
           ;; 2. a state file naming a key block the server cannot prove from does not bypass anything
           (let* ((fake-key (cl-ton::tl-block-id-ext :seqno 500 :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7)
                                                     :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 8)))
                  (shash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 9)))
             (%lite-put-octets path (cl-ton::%lite-state-octets zero fake-key shash))
             (let ((client (cl-ton:open-lite-client "127.0.0.1" port public zero :state-file path)))
               (unwind-protect
                    (progn (%lite-wait-ready client)
                           (check "a (self-consistent) file with an invented key block is loaded..."
                                  (= 500 (cl-ton::tl-get (cl-ton::lite-client-key-block client) :seqno)))
                           (check "...but the head can not be proved from it: the server's answer is refused"
                                  (handler-case (progn (cl-ton:lite-sync client) nil)
                                    (cl-ton:proof-error () t)
                                    (cl-ton:lite-error () t))))
                 (cl-ton:close-lite-client client))))
           ;; 3. the session is cut: the query waits for the reconnect and goes through
           (let ((client (cl-ton:open-lite-client "127.0.0.1" port public zero)))
             (unwind-protect
                  (progn
                    (%lite-wait-ready client)
                    (cl-ton:lite-sync client)
                    (let ((conn (cl-ton::adnl-ext-client-conn (cl-ton::lite-client-adnl client))))
                      (cl-ton::adnl-conn-close conn))
                    (check "after the connection was cut, a call is retried over the new session"
                           (getf (cl-ton:lite-account-state client addr) :exists))
                    (check "RETRY NIL does not wait for a reconnect"
                           (progn
                             (cl-ton::adnl-conn-close (cl-ton::adnl-ext-client-conn (cl-ton::lite-client-adnl client)))
                             (handler-case
                                 (progn (loop repeat 40 do (cl-ton:lite-call client (cl-ton::tl-make "liteServer.getMasterchainInfo") :retry nil
                                                                                                                                        :timeout 2)
                                                           (sleep 0.05))
                                        t)
                               (cl-ton::adnl-closed () t)
                               (cl-ton::adnl-timeout () t))))
                    (%lite-wait-ready client)
                    (check "the deadline bounds a call to a server that is gone"
                           (let ((dead (cl-ton:open-lite-client "127.0.0.1" 1 public zero)) (t0 (get-internal-real-time)))
                             (unwind-protect
                                  (and (handler-case (progn (cl-ton:lite-call dead (cl-ton::tl-make "liteServer.getMasterchainInfo")
                                                                                   :deadline 1.0)
                                                            nil)
                                         (cl-ton::adnl-closed () t)
                                         (cl-ton::adnl-timeout () t))
                                       (< (/ (- (get-internal-real-time) t0) internal-time-units-per-second) 4))
                               (cl-ton:close-lite-client dead)))))
               (cl-ton:close-lite-client client)))
           ;; 4. waiting for a block that is not there yet
           (let ((client (cl-ton:open-lite-client "127.0.0.1" port public zero)))
             (unwind-protect
                  (progn
                    (%lite-wait-ready client)
                    (let* ((target (+ (cl-ton::fc-head-seqno fc) 2))
                           (helper (sb-thread:make-thread (lambda () (sleep 0.4) (cl-ton::fakechain-advance fc 2)))))
                      (let ((head (cl-ton:lite-sync client :min-seqno target :wait-timeout 5)))
                        (sb-thread:join-thread helper)
                        (check "lite-sync :min-seqno waits for the block and proves a head at least that new"
                               (>= (cl-ton::tl-get head :seqno) target))))
                    (check "a block that never comes is an error after the wait, not a stale head"
                           (handler-case (progn (cl-ton:lite-sync client :min-seqno (+ 1000 (cl-ton::fc-head-seqno fc))
                                                                         :wait-timeout 0.3)
                                                nil)
                             (cl-ton:lite-error () t)
                             (cl-ton::ton-error () t))))
               (cl-ton:close-lite-client client))))))))

;;; --- the lite client as a drop-in for tonlib (plan R2b) --------------------------------------------
;;;
;;; The same TONLIB-* calls, made with the real tonlib client and with a lite client against the same
;;; fakechain, must return the same values.

(defun test-lite-backend-parity ()
  (format t "lite backend: the TONLIB-* functions on a lite client return what real tonlib returns~%")
  (if (not (%libs-available-p))
      (skip-missing "lite backend parity (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (cl-ton:wallet-address w))
                (absent (fake-address #x5a))
                (lib (cl-ton:end-cell (cl-ton:store-uint (cl-ton:begin-cell) 31337 32)))
                (hl (cl-ton::hex->octets (cl-ton::fakechain-add-library fc lib))))
           (cl-ton::fakechain-advance fc 4)
           (cl-ton::tonlib-sync tl)
           (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                  (lc (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc))))
             (unwind-protect
                  (progn
                    (%lite-wait-ready lc)
                    (flet ((same-cell (a b) (and a b (equalp (cl-ton::cell-hash-hex a) (cl-ton::cell-hash-hex b)))))
                      (check "masterchain info and block id: the same seqno and hashes"
                             (let ((tb (cl-ton:tonlib-masterchain-block tl)) (lb (cl-ton:tonlib-masterchain-block lc)))
                               (and (= (cl-ton:tonlib-masterchain-info tl) (cl-ton:tonlib-masterchain-info lc))
                                    (equalp (cl-ton:block-id-root-hash tb) (cl-ton:block-id-root-hash lb))
                                    (equalp (cl-ton:block-id-file-hash tb) (cl-ton:block-id-file-hash lb))
                                    (eql (cl-ton:block-id-shard tb) (cl-ton:block-id-shard lb))
                                    (eql (cl-ton:block-id-workchain tb) (cl-ton:block-id-workchain lb)))))
                      (dolist (a (list addr absent))
                        (let ((ts (cl-ton:tonlib-account-state tl a)) (ls (cl-ton:tonlib-account-state lc a)))
                          (check (format nil "account state of ~A: balance, code, data, last tx, status are the same"
                                         (if (eq a addr) "the wallet" "an absent account"))
                                 (and (= (cl-ton:account-state-balance ts) (cl-ton:account-state-balance ls))
                                      (eq (cl-ton:account-state-status ts) (cl-ton:account-state-status ls))
                                      (= (cl-ton:account-state-last-lt ts) (cl-ton:account-state-last-lt ls))
                                      (equal (cl-ton:account-state-last-hash ts) (cl-ton:account-state-last-hash ls))
                                      (or (and (null (cl-ton:account-state-code ts)) (null (cl-ton:account-state-code ls)))
                                          (same-cell (cl-ton:account-state-code ts) (cl-ton:account-state-code ls)))
                                      (or (and (null (cl-ton:account-state-data ts)) (null (cl-ton:account-state-data ls)))
                                          (same-cell (cl-ton:account-state-data ts) (cl-ton:account-state-data ls)))))))
                      (check "the configuration cell is the same"
                             (same-cell (cl-ton:tonlib-config-cell tl) (cl-ton:tonlib-config-cell lc)))
                      (dolist (a (list addr absent))
                        (check (format nil "the ShardAccount cell of ~A is the same" (if (eq a addr) "the wallet" "an absent account"))
                               (same-cell (cl-ton::tonlib-shard-account-cell tl a) (cl-ton::tonlib-shard-account-cell lc a))))
                      (check "the libraries are the same, an unpublished hash is left out by both"
                             (let ((tx (cl-ton:tonlib-libraries tl (list hl (cl-ton::sha256 (make-array 3 :element-type '(unsigned-byte 8) :initial-contents '(1 2 3))))))
                                   (lx (cl-ton:tonlib-libraries lc (list hl (cl-ton::sha256 (make-array 3 :element-type '(unsigned-byte 8) :initial-contents '(1 2 3)))))))
                               (and (= 1 (length tx) (length lx))
                                    (string-equal (car (first tx)) (car (first lx)))
                                    (same-cell (cdr (first tx)) (cdr (first lx))))))
                      (check "a getter run gives the same stack and exit code (the wallet's seqno)"
                             (multiple-value-bind (ti te) (cl-ton:tonlib-run-get-method tl addr "seqno" nil)
                               (multiple-value-bind (li le) (cl-ton:tonlib-run-get-method lc addr "seqno" nil)
                                 (and (eql te le) (equalp (mapcar #'cl-ton:stack-item-key ti)
                                                          (mapcar #'cl-ton:stack-item-key li))))))
                      (check "the local getter (emulator on fetched code) works on a lite client too"
                             (let ((g (cl-ton:make-local-getter lc (cl-ton:tonlib-config-cell lc))))
                               (equalp (mapcar #'cl-ton:stack-item-key (funcall g addr "seqno" nil))
                                       (mapcar #'cl-ton:stack-item-key (nth-value 0 (cl-ton:tonlib-run-get-method tl addr "seqno" nil))))))
                      (check "the hash tonlib returns for a sent message is the one the lite client computes"
                             (let* ((msg (%transfer w 0 (fake-address #x66) (cl-ton::nano 1/10)))
                                    (boc (cl-ton::serialize-boc msg))
                                    (t-hash (cl-ton:tonlib-send-message tl msg)))
                               (equal t-hash (cl-ton::base64-encode (cl-ton::external-message-hash boc)))))
                      (check "...and a message sent through the lite client is accepted, with that hash"
                             (let* ((msg (%transfer w 1 (fake-address #x67) (cl-ton::nano 1/10))))
                               (equal (cl-ton:tonlib-send-message lc msg)
                                      (cl-ton::base64-encode (cl-ton::external-message-hash (cl-ton::serialize-boc msg))))))))
               (cl-ton:close-lite-client lc))))))))

(defun %json-diff (a b &optional (path ""))
  "The paths at which the JSON-shaped values A and B differ (hash tables compared key by key)."
  (cond ((and (hash-table-p a) (hash-table-p b))
         (let ((out '()))
           (maphash (lambda (k v) (setf out (append out (%json-diff v (gethash k b) (format nil "~A/~A" path k))))) a)
           (maphash (lambda (k v) (declare (ignore v)) (unless (nth-value 1 (gethash k a)) (push (format nil "~A/~A (only in 2nd)" path k) out))) b)
           out))
        ((and (listp a) (listp b) (not (and (null a) (null b))))
         (if (/= (length a) (length b))
             (list (format nil "~A: ~D vs ~D elements" path (length a) (length b)))
             (loop for x in a for y in b for i from 0 append (%json-diff x y (format nil "~A[~D]" path i)))))
        ((equalp a b) nil)
        ((and (member a '(nil "")) (member b '(nil ""))) nil)
        (t (list (format nil "~A: ~S vs ~S" path (if (stringp a) (subseq a 0 (min 60 (length a))) a)
                         (if (stringp b) (subseq b 0 (min 60 (length b))) b))))))

(defun %tx-normalize (tx)
  "A copy of the typed raw.transaction TX whose DATA (a BoC) is replaced by the hash of its cell: two BoC byte
layouts of one cell are the same data."
  (let ((fields (copy-list (cl-ton::tlapi-obj-fields tx))))
    (setf (getf fields :data)
          (cl-ton::cell-hash (first (cl-ton::parse-boc (cl-ton:raw-tx-data tx)))))
    (cl-ton::%make-tlapi-obj (cl-ton::tlapi-obj-name tx) fields)))

(defun test-lite-backend-parity-2 ()
  (format t "lite backend: shards, block transactions and raw transactions against real tonlib~%")
  (if (not (%libs-available-p))
      (skip-missing "lite backend parity 2 (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore proxy cfg))
         (let* ((w (%seed-wallet fc)) (addr (cl-ton:wallet-address w)) (dest (fake-address #x66)))
           (dotimes (seqno 3)
             (%fc-enqueue fc (%transfer w seqno dest (cl-ton::nano 1/10)))
             (cl-ton::fakechain-advance fc 2))
           (cl-ton::tonlib-sync tl)
           (let* ((public (cl-ton::keypair-public (cl-ton::fakechain-keypair fc)))
                  (lc (cl-ton:open-lite-client "127.0.0.1" (cl-ton::fakechain-port fc) public (%zero-block-id fc))))
             (unwind-protect
                  (progn
                    (%lite-wait-ready lc)
                    (let* ((head-json (cl-ton:tonlib-masterchain-block tl))
                           (t-shards (cl-ton:tonlib-shards tl head-json))
                           (l-shards (cl-ton:tonlib-shards lc head-json)))
                      (check "the shards of the head are the same typed block ids"
                             (and (plusp (length t-shards))
                                  (equalp (mapcar #'cl-ton::tlapi-obj-fields t-shards)
                                          (mapcar #'cl-ton::tlapi-obj-fields l-shards)))))
                    (let ((all-same t) (seen 0) (shown nil))
                      (loop for seqno from 1 to (cl-ton::fc-head-seqno fc)
                            do (let* ((mc (cl-ton::lite-block-id->tlapi (cl-ton::fc-mc-id (cl-ton::fc-find-block fc seqno)))))
                                 (dolist (sh (cl-ton:tonlib-shards tl mc))
                                   (let ((tt (cl-ton:tonlib-block-transactions tl sh :count nil))
                                         (lt (cl-ton:tonlib-block-transactions lc sh :count nil)))
                                     (incf seen (length tt))
                                     (unless (and (= (length tt) (length lt))
                                                  (equalp (mapcar #'cl-ton::tlapi-obj-fields tt)
                                                          (mapcar #'cl-ton::tlapi-obj-fields lt)))
                                       (setf all-same nil)
                                       (unless shown
                                         (setf shown (list (format nil "tonlib ~D ids, lite ~D ids" (length tt) (length lt))))))))))
                      (when shown (format t "    first differences: ~{~A~^; ~}~%" (subseq shown 0 (min 5 (length shown)))))
                      (check (format nil "the short transaction ids of every block are the same (~D transactions seen)" seen)
                             (and all-same (plusp seen))))
                    (check "block transactions with a page size: counted pages join up"
                           (let* ((sh (first (cl-ton:tonlib-shards tl (cl-ton:tonlib-masterchain-block tl))))
                                  (a (cl-ton:tonlib-block-transactions lc sh :count 1)))
                             (<= (length a) 1)))
                    (let* ((tt (mapcar #'%tx-normalize (cl-ton:tonlib-transactions tl addr)))
                           (lt (mapcar #'%tx-normalize (cl-ton:tonlib-transactions lc addr))))
                      (let ((same (and (= (length tt) (length lt)) (every #'%tlapi-equal tt lt))))
                        (unless same
                          (format t "    tonlib ~D transactions, lite ~D~%" (length tt) (length lt)))
                        (check (format nil "the wallet's raw transactions are the same objects (~D of them)" (length tt))
                               (and same (plusp (length tt))))))
                    (check "...also when asked from an older transaction id"
                           (let* ((tt (cl-ton:tonlib-transactions tl addr)) (second-tx (second tt)))
                             (and second-tx
                                  (let* ((from-lt (cl-ton:raw-tx-lt second-tx)) (from-hash (cl-ton:raw-tx-hash second-tx))
                                         (a (mapcar #'%tx-normalize (cl-ton:tonlib-transactions tl addr :from-lt from-lt :from-hash from-hash)))
                                         (b (mapcar #'%tx-normalize (cl-ton:tonlib-transactions lc addr :from-lt from-lt :from-hash from-hash))))
                                    (and (= (length a) (length b)) (every #'%tlapi-equal a b)))))))
               (cl-ton:close-lite-client lc))))))))

(defun test-diagnose-lite ()
  (format t "lite backend: the real-network diagnostic, run against the fakechain~%")
  (if (not (%libs-available-p))
      (skip-missing "lite diagnostic (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy))
         (let* ((w (%seed-wallet fc)) (addr (cl-ton:wallet-address w)))
           (%fc-enqueue fc (%transfer w 0 (fake-address #x66) (cl-ton::nano 1/10)))
           (cl-ton::fakechain-advance fc 6)
           (multiple-value-bind (ok report)
               (cl-ton:diagnose-lite cfg :account (cl-ton::address->string addr) :getter "seqno" :stream nil
                                         :sync-total-timeout 60 :timeout 20)
             (check "the diagnostic passes against a healthy chain" ok)
             (unless ok (format t "~A~%" report))
             (check "...and reports every step"
                    (every (lambda (s) (search s report))
                           '("sync from the init block" "masterchain head" "account state" "getter" "configuration"
                             "shards of the head" "transactions of a shard block" "transactions of the account"
                             "proof of an older masterchain block" "block lookup by time" "RESULT: OK")))
             (check "...names the ironclad assembly optimizer, which must be on"
                    (search "ironclad SBCL assembly optimizer: on" report))
             (check "...and says what became of the link vectors (kept, or none captured), without failing"
                    (and (search "link vector" report) (not (search "link vectors not saved" report))))))))))
