;;;; fake-world.lisp -- the fake network populated with the real DEX contracts.
;;;;
;;;; The emulator can run a router, pool or vault only with the real code and data cells, which exist only on the live chain.
;;;; They were captured once (tests/fixtures/dex/<address>.json + manifest.json: STON.fi v1 and v2, DeDust, jetton masters, pTON);
;;;; FNET-LOAD-DEX-WORLD seeds a FAKE-NETWORK with them at their original addresses, so a strategy test reads pools and runs
;;;; their getters through the typed lite API, and a message to a router executes in the emulator as on a node.  Fixture
;;;; directory: $TON_TRADER_DEX_FIXTURES, else <project>/tests/fixtures/dex/.  Where the directory is absent the world is NIL and
;;;; a test skips (never fails).

(in-package :cl-ton/test)

(defun dex-fixtures-directory ()
  "The directory of the captured DEX contracts, or NIL when there is none."
  (let* ((env (uiop:getenv "TON_TRADER_DEX_FIXTURES"))
         (dir (if (and env (plusp (length env)))
                  (uiop:ensure-directory-pathname env)
                  (ignore-errors (asdf:system-relative-pathname "cl-ton" "../tests/fixtures/dex/")))))
    (and dir (probe-file (merge-pathnames "manifest.json" dir)) dir)))

(defstruct (dex-world (:conc-name dw-) (:copier nil))
  directory
  addresses                             ; address strings of every captured contract
  pools)                                ; list of (DEX . pool address string), dex = "stonfi-v1" "stonfi-v2" "dedust"

(defun fnet-load-dex-world (net &key (directory (dex-fixtures-directory)))
  "Seed NET with every captured contract at its original address; returns a DEX-WORLD, or NIL when there are no fixtures."
  (when directory
    (let* ((manifest (cl-ton::json-decode (uiop:read-file-string (merge-pathnames "manifest.json" directory))))
           (addresses (coerce (cl-ton::json-get manifest "captured") 'list))
           (pools (mapcar (lambda (p) (cons (cl-ton::json-get p "dex") (cl-ton::json-get p "pool")))
                          (coerce (cl-ton::json-get manifest "pools") 'list))))
      (dolist (a addresses)
        (cl-ton::fakechain-load-fixture (fnet-chain net) (merge-pathnames (format nil "~A.json" a) directory)))
      (fnet-advance net 1)                   ; seeded accounts are in a sealed block: provable from now on
      (make-dex-world :directory directory :addresses addresses :pools pools))))

(defun fnet-get-method (net address method &optional stack)
  "Run the getter METHOD (a name) of ADDRESS (a string or an address) at the head, through the typed liteServer.runSmcMethod;
returns (VALUES EXIT-CODE STACK-ITEMS)."
  (let* ((addr (if (stringp address) (cl-ton:parse-address address) address))
         (answer (fnet-execute net (cl-ton::tl-make "liteServer.runSmcMethod" :mode 4 :id (cl-ton::lite-sync (fnet-client net))
                                                    :account (%lite-account-id addr) :method-id (cl-ton::method-id method)
                                                    :params (cl-ton:serialize-boc (list (cl-ton::serialize-vm-stack stack))
                                                                                  :has-crc32c nil)))))
    (values (cl-ton::tl-get answer :exit-code)
            (and (zerop (cl-ton::tl-get answer :exit-code))
                 (cl-ton::parse-vm-stack (first (cl-ton::parse-boc (cl-ton::tl-get answer :result))))))))

(defun fnet-jetton-wallet-address (net master owner)
  "The address the jetton MASTER (an address or string) gives to the jetton wallet of OWNER (an address): its get_wallet_address."
  (multiple-value-bind (exit stack)
      (fnet-get-method net master "get_wallet_address"
                       (list (cl-ton::cell-slice (cl-ton:end-cell (cl-ton::store-address (cl-ton:begin-cell) owner)))))
    (unless (zerop exit) (cl-ton::ton-error "get_wallet_address exited with ~D" exit))
    (values (cl-ton::load-address (cl-ton::stack-slice (first stack))))))

(defun fnet-deploy-jetton-wallet (net master owner balance &key (ton (cl-ton::nano 1)))
  "Put a jetton wallet of OWNER holding BALANCE (the jetton's smallest unit) into NET, for the jetton MASTER, whose code the
master itself reports (get_jetton_data).  The stablecoin storage layout (status:uint4 balance:Coins owner master) is used and
CHECKED: the address of the code and data must be the one the master computes for OWNER, else this signals.  Returns the address."
  (let* ((master-addr (if (stringp master) (cl-ton:parse-address master) master)))
    (multiple-value-bind (exit stack) (fnet-get-method net master-addr "get_jetton_data")
      (unless (zerop exit) (cl-ton::ton-error "get_jetton_data exited with ~D" exit))
      (let* ((code (fifth stack))
             (data-with (lambda (balance)
                          (cl-ton:end-cell
                           (cl-ton::store-address
                            (cl-ton::store-address
                             (cl-ton::store-coins (cl-ton:store-uint (cl-ton:begin-cell) 0 4) balance)
                             owner)
                            master-addr))))
             ;; the ADDRESS comes from the INITIAL state (balance 0), the account holds the state it has now
             (address (cl-ton::state-init-address (cl-ton::make-state-init code (funcall data-with 0))))
             (expected (fnet-jetton-wallet-address net master-addr owner)))
        (unless (cl-ton::address-equal address expected)
          (cl-ton::ton-error "the jetton wallet layout does not match the master: ~A against ~A"
                             (cl-ton:address->string address) (cl-ton:address->string expected)))
        (cl-ton::fakechain-set-account (fnet-chain net) address
                                       :state-init (cl-ton::make-state-init code (funcall data-with balance))
                                       :balance ton)
        (fnet-advance net 1)                 ; the new account is in a sealed block: provable from now on
        address))))

(defun %dex-pool-getter (dex)
  (if (string= dex "dedust") "get_reserves" "get_pool_data"))

(defun test-fake-world ()
  (format t "fake world: the captured DEX contracts on the fake network, read and run through the typed lite API~%")
  (cond
    ((not (%libs-available-p)) (skip-missing "the fake world (emulator shared library)"))
    ((not (dex-fixtures-directory)) (skip-missing "the fake world (no DEX fixtures: tests/fixtures/dex)"))
    (t
     (with-fake-network (net :blocks 2)
       (let ((world (fnet-load-dex-world net)))
         (fnet-advance net 2)
         (check "fake world: every captured contract is on the network with its code, proved"
                (every (lambda (a)
                         (let ((state (cl-ton::tl-get (fnet-account net (cl-ton:parse-address a)) :state)))
                           (plusp (length state))))
                       (dw-addresses world)))
         (dolist (pool (dw-pools world))
           (multiple-value-bind (exit stack) (fnet-get-method net (cdr pool) (%dex-pool-getter (car pool)))
             (check (format nil "fake world: the ~A pool ~A runs its getter ~A on the proved state"
                            (car pool) (subseq (cdr pool) 0 8) (%dex-pool-getter (car pool)))
                    (and (zerop exit) (plusp (length stack))))))
         (let ((usdt (find-if (lambda (a) (search "EQCxE6mU" a)) (dw-addresses world))))
           (when usdt
             (multiple-value-bind (exit stack) (fnet-get-method net usdt "get_jetton_data")
               (check "fake world: the USDT jetton master answers get_jetton_data (supply, mintable, admin, content, wallet code)"
                      (and (zerop exit) (= 5 (length stack))))))
           (when usdt
             (let* ((w (fnet-fund-wallet net :balance (cl-ton::nano 5)))
                    (owner (cl-ton:wallet-address w))
                    (jw (fnet-deploy-jetton-wallet net usdt owner 1000000000)))
               (fnet-advance net 2)
               (multiple-value-bind (exit stack) (fnet-get-method net jw "get_wallet_data")
                 (check "fake world: a jetton wallet of the scenario wallet holds 1000 USDT, at the address the master computes"
                        (and (zerop exit) (= 1000000000 (first stack))))))))))))
  )
