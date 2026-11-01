;;;; scenario-kit.lisp -- build a world, send a typed message, step blocks, assert.
;;;;
;;;; The pieces a strategy test uses on a FAKE-NETWORK (fake-network.lisp) with the DEX world loaded (fake-world.lisp):
;;;; a wallet sends messages (FNET-WALLET-SEND, the seqno read from the wallet's own getter), jettons move between owners
;;;; (FNET-SEND-JETTONS), time passes only on FNET-ADVANCE, and the result is read back through the typed lite API only
;;;; (FNET-BALANCE, FNET-JETTON-BALANCE, FNET-GET-METHOD, liteServer.getTransactions).  Every message executes in the
;;;; emulator as it would on a node: the whole cascade (wallet -> jetton wallet -> recipient's jetton wallet) runs.

(in-package :cl-ton/test)

(defun fnet-wallet-seqno (net wallet)
  "The seqno the wallet's own getter reports at the head."
  (multiple-value-bind (exit stack) (fnet-get-method net (cl-ton:wallet-address wallet) "seqno")
    (unless (zerop exit) (cl-ton::ton-error "the wallet seqno getter exited with ~D" exit))
    (first stack)))

(defun fnet-wallet-send (net wallet &rest specs)
  "Send one external message of WALLET carrying the MESSAGE-SPECs, with the seqno the wallet reports; returns the typed
liteServer.sendMsgStatus.  Nothing executes until the network is advanced."
  (fnet-send net (cl-ton:wallet-external-message wallet :seqno (fnet-wallet-seqno net wallet) :messages specs)))

(defun fnet-send-jettons (net wallet jetton-wallet amount destination &key (ton (cl-ton::nano 1/5)) (forward-ton 0))
  "WALLET asks its JETTON-WALLET (an address) to move AMOUNT jettons to the owner DESTINATION, attaching TON for the fees;
the excess returns to WALLET."
  (fnet-wallet-send net wallet
                    (cl-ton:make-message-spec :to jetton-wallet :value ton :bounce t
                                              :body (cl-ton::jetton-transfer-body
                                                     :amount amount :destination destination
                                                     :response-destination (cl-ton:wallet-address wallet)
                                                     :forward-ton-amount forward-ton))))

(defun fnet-jetton-balance (net master owner)
  "The jettons of the jetton MASTER that OWNER holds, read out of its jetton wallet (0 when that wallet does not exist)."
  (let ((jw (fnet-jetton-wallet-address net master owner)))
    (if (zerop (length (cl-ton::tl-get (fnet-account net jw) :state)))
        0
        (multiple-value-bind (exit stack) (fnet-get-method net jw "get_wallet_data")
          (if (zerop exit) (first stack) 0)))))

(defun test-scenario-jetton-transfer ()
  (format t "scenario: a jetton transfer between two owners through the real USDT contracts~%")
  (cond
    ((not (%libs-available-p)) (skip-missing "the jetton scenario (emulator shared library)"))
    ((not (dex-fixtures-directory)) (skip-missing "the jetton scenario (no DEX fixtures)"))
    (t
     (with-fake-network (net :blocks 2)
       (let* ((world (fnet-load-dex-world net))
              (usdt (cl-ton:parse-address (find-if (lambda (a) (search "EQCxE6mU" a)) (dw-addresses world))))
              (w (fnet-fund-wallet net :balance (cl-ton::nano 5)))
              (owner (cl-ton:wallet-address w))
              (friend (fake-address #x55))
              (jw (fnet-deploy-jetton-wallet net usdt owner 1000000000)))
         (fnet-advance net 2)
         (check "scenario: the wallet starts with 1000 USDT and the friend with none"
                (and (= 1000000000 (fnet-jetton-balance net usdt owner))
                     (zerop (fnet-jetton-balance net usdt friend))))
         (let ((status (fnet-send-jettons net w jw 250000000 friend)))
           (check "scenario: the transfer message is accepted into the pool"
                  (= 1 (cl-ton::tl-get status :status))))
         (check "scenario: nothing moved before a block was sealed"
                (= 1000000000 (fnet-jetton-balance net usdt owner)))
         (fnet-advance net 6)
         (check "scenario: the cascade ran: 250 USDT left the sender's jetton wallet"
                (= 750000000 (fnet-jetton-balance net usdt owner)))
         (check "scenario: and arrived in the friend's jetton wallet, deployed by the transfer"
                (= 250000000 (fnet-jetton-balance net usdt friend)))
         (check "scenario: the wallet's seqno advanced and it paid the TON fees"
                (and (= 1 (fnet-wallet-seqno net w))
                     (< (fnet-balance net owner) (cl-ton::nano 5)))))))))
