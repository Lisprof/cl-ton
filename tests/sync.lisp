;;;; sync.lisp -- tests for sync.lisp: validator sets, signature checking, forward block links.
;;;;
;;;; The weight arithmetic and every strictness rule are tested on hand-built validator sets (the
;;;; fakechain has one validator of weight 1).  The chain itself is tested end to end against the
;;;; fakechain: from the zero state, through a verified link, to a verified account.

(in-package :cl-ton/test)

(defvar *sync-state* (sb-ext:seed-random-state 20261011))
(defun %srnd (n) (random n *sync-state*))

(defun %vkey (i)
  "A deterministic test validator keypair number I."
  (cl-ton::seed->keypair (make-array 32 :element-type '(unsigned-byte 8) :initial-element (+ 100 i))))

(defun %vset-cell (keypairs weights &key (tag #x12) (since 0) (until #xffffffff) main total-weight)
  "A validator set parameter cell with the given validators (in list order)."
  (let* ((n (length keypairs)) (main (or main n))
         (stated (or total-weight (reduce #'+ weights)))
         (entries (loop for kp in keypairs for w in weights for i from 0
                        collect (cons i (let ((kp kp) (w w))
                                          (lambda (vb)
                                            (cl-ton:store-uint
                                             (cl-ton:store-bytes (cl-ton:store-uint (cl-ton:store-uint vb #x53 8) #x8e81278a 32)
                                                                 (cl-ton::keypair-public kp))
                                             w 64))))))
         (b (cl-ton:store-uint (cl-ton:store-uint (cl-ton:store-uint (cl-ton:store-uint (cl-ton:store-uint
                                (cl-ton:begin-cell) tag 8) since 32) until 32) n 16) main 16)))
    (cl-ton:end-cell
     (if (= tag #x12)
         (cl-ton::store-dict (cl-ton:store-uint b stated 64) entries 16)
         (cl-ton:store-ref b (cl-ton::hashmap-cell entries 16))))))

(defun %block-id (&optional (seed 1))
  (cl-ton::tl-block-id-ext :workchain -1 :shard (- (expt 2 63)) :seqno seed
                           :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element seed)
                           :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element (+ seed 1))))

(defun %sign (kp block-id)
  (cl-ton::sign-octets kp (cl-ton::tl-encode (cl-ton::tl-make "ton.blockId" :root-cell-hash (cl-ton::tl-get block-id :root-hash)
                                                              :file-hash (cl-ton::tl-get block-id :file-hash)))))

(defun %sig-entry (kp &optional signature)
  (cl-ton::tl-make "liteServer.signature" :node-id-short (cl-ton::adnl-short-id (cl-ton::keypair-public kp))
                                          :signature (or signature nil)))

(defun %sigset (block-id signers &key (name "liteServer.signatureSet.ordinary"))
  "A signature set where each of SIGNERS (keypairs) signs BLOCK-ID."
  (cl-ton::tl-make name :validator-set-hash 0 :catchain-seqno 0
                        :signatures (coerce (mapcar (lambda (kp) (%sig-entry kp (%sign kp block-id))) signers) 'vector)))

(defun %zero-block-id (fc)
  "The zero state's BLOCK id (seqno 0), where a client's sync starts: its root hash is the zero
state's own hash, which is what the client's global config names."
  (cl-ton::tl-block-id-ext :seqno 0 :root-hash (cl-ton::fakechain-zero-root fc)
                           :file-hash (cl-ton::fakechain-zero-file fc)))

(defun test-validator-sets ()
  (format t "sync: validator sets and signature weights~%")
  (let* ((k (mapcar #'%vkey '(0 1 2 3)))
         (id (%block-id))
         (vset3 (cl-ton:parse-validator-set (%vset-cell (subseq k 0 3) '(1 1 1)))))
    (check "a validator_ext set parses: window, main count, total weight, members with their short ids"
           (and (= 0 (cl-ton:validator-set-since vset3)) (= #xffffffff (cl-ton:validator-set-until vset3))
                (= 3 (cl-ton:validator-set-main vset3)) (= 3 (cl-ton:validator-set-total-weight vset3))
                (= 3 (length (cl-ton:validator-set-members vset3)))
                (equalp (first (aref (cl-ton:validator-set-members vset3) 0))
                        (cl-ton::adnl-short-id (cl-ton::keypair-public (first k))))))
    (check "a plain validators#11 set parses too"
           (= 3 (cl-ton:validator-set-total-weight
                 (cl-ton:parse-validator-set (%vset-cell (subseq k 0 3) '(1 1 1) :tag #x11)))))
    (check "mainnet shape: the stated total weight covers all validators, the signing weight only the main ones"
           (let ((v (cl-ton:parse-validator-set (%vset-cell (subseq k 0 4) '(4 5 6 7) :main 2 :total-weight 22))))
             (and (= 2 (length (cl-ton:validator-set-members v))) (= 9 (cl-ton:validator-set-total-weight v)))))
    (check "only the main validators count: 3 listed, main 2, the third is not a member"
           (let ((v (cl-ton:parse-validator-set (%vset-cell (subseq k 0 3) '(4 5 6) :main 2))))
             (and (= 2 (length (cl-ton:validator-set-members v))) (= 9 (cl-ton:validator-set-total-weight v)))))
    (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
      (refuses "a stated total weight that is not the sum over all the validators"
               (cl-ton:parse-validator-set (%vset-cell (subseq k 0 3) '(1 1 1) :total-weight 4)))
      (refuses "more main validators than validators" (cl-ton:parse-validator-set (%vset-cell (subseq k 0 2) '(1 1) :main 3)))
      (refuses "a validator of weight 0" (cl-ton:parse-validator-set (%vset-cell (subseq k 0 2) '(1 0))))
      (refuses "the same key listed twice" (cl-ton:parse-validator-set (%vset-cell (list (first k) (first k)) '(1 1))))
      (refuses "something that is not a validator set" (cl-ton:parse-validator-set (%vset-cell (subseq k 0 1) '(1) :tag #x13))))
    (check "the validity window: since <= time < until"
           (let ((v (cl-ton:parse-validator-set (%vset-cell (subseq k 0 1) '(1) :since 100 :until 200))))
             (and (not (cl-ton:validator-set-active-p v 99)) (cl-ton:validator-set-active-p v 100)
                  (cl-ton:validator-set-active-p v 199) (not (cl-ton:validator-set-active-p v 200)))))
    ;; the two-thirds rule, strictly more than
    (check "weights 1,1,1: all three signing passes, two do not (2/3 is not MORE than 2/3)"
           (and (cl-ton:check-block-signatures vset3 id (%sigset id (subseq k 0 3)))
                (%signals cl-ton:proof-error (cl-ton:check-block-signatures vset3 id (%sigset id (subseq k 0 2))))))
    (let ((v4 (cl-ton:parse-validator-set (%vset-cell k '(1 1 1 1)))))
      (check "weights 1,1,1,1: three of four pass, two do not"
             (and (cl-ton:check-block-signatures v4 id (%sigset id (subseq k 0 3)))
                  (%signals cl-ton:proof-error (cl-ton:check-block-signatures v4 id (%sigset id (subseq k 0 2)))))))
    (let ((v (cl-ton:parse-validator-set (%vset-cell (subseq k 0 3) '(5 1 1)))))
      (check "weights 5,1,1: the heavy validator alone passes (15 > 14), the two light ones do not"
             (and (= 5 (cl-ton:check-block-signatures v id (%sigset id (list (first k)))))
                  (%signals cl-ton:proof-error (cl-ton:check-block-signatures v id (%sigset id (cdr (subseq k 0 3))))))))
    (check "no signatures at all do not pass"
           (%signals cl-ton:proof-error (cl-ton:check-block-signatures vset3 id (%sigset id '()))))
    ;; every strictness rule
    (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
      (refuses "a signer signing twice (it would count twice)"
               (cl-ton:check-block-signatures vset3 id (%sigset id (list (first k) (first k) (second k) (third k)))))
      (refuses "a signature by someone outside the set, even with all members signing"
               (cl-ton:check-block-signatures vset3 id (%sigset id (list (first k) (second k) (third k) (fourth k)))))
      (refuses "one invalid signature among valid ones (a bit flipped)"
               (let* ((good (%sigset id (subseq k 0 3)))
                      (sigs (copy-seq (cl-ton::tl-get good :signatures)))
                      (bad (cl-ton::tl-get (aref sigs 1) :signature)))
                 (setf (aref sigs 1) (%sig-entry (second k) (%flip-octet bad 5)))
                 (cl-ton:check-block-signatures vset3 id (cl-ton::tl-make "liteServer.signatureSet.ordinary"
                                                                          :validator-set-hash 0 :catchain-seqno 0 :signatures sigs))))
      (refuses "signatures over a different block"
               (cl-ton:check-block-signatures vset3 id (%sigset (%block-id 9) (subseq k 0 3))))
      (refuses "a signature of the wrong length"
               (cl-ton:check-block-signatures
                vset3 id (cl-ton::tl-make "liteServer.signatureSet.ordinary" :validator-set-hash 0 :catchain-seqno 0
                                          :signatures (vector (%sig-entry (first k) (subseq (%sign (first k) id) 0 63))))))
      (refuses "a signature set of a type this code does not know"
               (cl-ton:check-block-signatures vset3 id (cl-ton::tl-make "liteServer.signatureSet.simplex" :cc-seqno 0 :validator-set-hash 0
                                                                      :signatures (vector) :session-id (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)
                                                                      :slot 0 :candidate (make-array 0 :element-type '(unsigned-byte 8)))))))
  (test-simplex-signatures)
  (test-ironclad-assembly)
  (test-real-link-vectors))

;;; --- ironclad's SBCL assembly optimizer ----------------------------------------------------------

(defun %hex-octets (hex)
  (let ((v (make-array (floor (length hex) 2) :element-type '(unsigned-byte 8))))
    (dotimes (i (length v) v) (setf (aref v i) (parse-integer hex :start (* 2 i) :end (+ 2 (* 2 i)) :radix 16)))))

(defun test-ironclad-assembly ()
  (format t "ironclad: the SBCL assembly optimizer is on, and what it computes is right~%")
  (let ((status (cl-ton:ironclad-assembly-status)))
    (check "ironclad was built with :ironclad-assembly (AES-NI / PCLMULQDQ VOPs, fast rotates)" (getf status :assembly))
    (check "its VOP package IRONCLAD-VM is loaded" (getf status :vm-package))
    (check "the diagnostics line says so" (search "optimizer: on" (cl-ton:ironclad-assembly-line)))
    (format t "  (~A)~%" (cl-ton:ironclad-assembly-line)))
  ;; NIST SP 800-38A F.5.5 (CTR-AES256), the cipher of every ADNL-ext connection: the AES-NI path, when the
  ;; CPU has it, must give the standard's answer on one call over four blocks and on block-by-block calls
  (let* ((key (%hex-octets "603deb1015ca71be2b73aef0857d77811f352c073b6108d72d9810a30914dff4"))
         (iv (%hex-octets "f0f1f2f3f4f5f6f7f8f9fafbfcfdfeff"))
         (plain (%hex-octets "6bc1bee22e409f96e93d7e117393172aae2d8a571e03ac9c9eb76fac45af8e5130c81c46a35ce411e5fbc1191a0a52eff69f2445df4f9b17ad2b417be66c3710"))
         (expect (%hex-octets "601ec313775789a5b7a7f504bbf3d228f443e3ca4d62b59aca84e990cacaf5c52b0930daa23de94ce87017ba2d84988ddfc9c58db67aada613c2dd08457941a6"))
         (whole (copy-seq plain))
         (pieces (copy-seq plain))
         (c1 (cl-ton::adnl-make-cipher key iv))
         (c2 (cl-ton::adnl-make-cipher key iv)))
    (ironclad:encrypt-in-place c1 whole)
    (loop for i from 0 below 64 by 16 do (ironclad:encrypt-in-place c2 pieces :start i :end (+ i 16)))
    (check "AES-256-CTR over four blocks equals NIST SP 800-38A F.5.5" (equalp whole expect))
    (check "...and so does the same stream applied block by block" (equalp pieces expect))
    (check "...and the cipher is its own inverse (ADNL uses one function for both directions)"
           (let ((back (copy-seq whole)) (c3 (cl-ton::adnl-make-cipher key iv)))
             (ironclad:encrypt-in-place c3 back)
             (equalp back plain)))))

;;; --- real mainnet links ---------------------------------------------------------------------------
;;;
;;; cl-ton/tests/fixtures/real/link-<kind>-<from>-<to>.bin/.sexp: single forward links of the real mainnet
;;; key-block chain, cut out of the proofs a liteserver answered and verified by TON_TRADER_LITE_DIAGNOSE (which
;;; keeps them in <keystore>/capture/).  The Simplex ones are the reference for the new consensus's signed
;;; message: everything the synthetic sets below can only imitate is checked here on data the network produced.

(defun %real-vector-dir ()
  (let ((e (uiop:getenv "TON_TRADER_REAL_VECTORS")))
    (if (and e (plusp (length e)))
        (uiop:ensure-directory-pathname e)
        (merge-pathnames "fixtures/real/" (make-pathname :name nil :type nil :version nil :defaults #.(or *compile-file-truename* *load-truename*))))))

(defun %flip-byte (octets index)
  (let ((v (copy-seq octets))) (setf (aref v index) (logxor (aref v index) #x40)) v))

(defun %vector-refused-p (thunk)
  "True when THUNK is refused with a proof-error; an error of another kind is let through."
  (handler-case (progn (funcall thunk) nil)
    (cl-ton:proof-error () t)))

(defun %check-link-vector (bin)
  "All the checks of one link vector, BIN a link-*.bin path (as written by SAVE-LINK-VECTOR)."
  (multiple-value-bind (known proof meta) (cl-ton:load-link-vector bin)
    (let* ((kind (getf meta :kind)) (name (file-namestring bin))
           (link (aref (cl-ton::tl-get proof :steps) 0))
           (set (cl-ton::tl-get link :signatures))
           (sigs (cl-ton::tl-get set :signatures))
           (counts (list :ordinary 0 :simplex 0))
           (result (let ((cl-ton::*signature-set-counts* counts)) (cl-ton:verify-partial-block-proof proof known))))
      (flet ((refused-with (&rest fields)
               ;; the proof with the signature set's FIELDS replaced
               (%vector-refused-p (lambda ()
                                    (cl-ton:verify-partial-block-proof
                                     (%obj-with proof :steps (vector (%obj-with link :signatures (apply #'%obj-with set fields))))
                                     known)))))
        (check (format nil "~A: the link verifies from its start block" name)
               (and (= 1 (getf result :steps)) (= (getf meta :to-seqno) (cl-ton::tl-get (getf result :to) :seqno))))
        (check (format nil "~A: it carries one ~(~A~) signature set, as its description says" name kind)
               (and (= 1 (getf counts kind)) (= 0 (getf counts (if (eq kind :simplex) :ordinary :simplex)))))
        (check (format nil "~A: from another start block it is refused" name)
               (%vector-refused-p (lambda () (cl-ton:verify-partial-block-proof
                                              proof (cl-ton::tl-block-id-ext
                                                     :workchain -1 :seqno (cl-ton::tl-get known :seqno)
                                                     :root-hash (%flip-byte (cl-ton::tl-get known :root-hash) 0)
                                                     :file-hash (cl-ton::tl-get known :file-hash))))))
        (check (format nil "~A: with one signature damaged it is refused" name)
               (let ((bad (%obj-with (aref sigs 0) :signature (%flip-byte (cl-ton::tl-get (aref sigs 0) :signature) 5))))
                 (refused-with :signatures (concatenate 'vector (vector bad) (subseq sigs 1)))))
        (check (format nil "~A: with fewer signatures than two thirds of the weight it is refused" name)
               (refused-with :signatures (subseq sigs 0 (floor (length sigs) 3))))
        (check (format nil "~A: with another validator-set hash it is refused" name)
               (refused-with :validator-set-hash (logxor 1 (cl-ton::tl-get set :validator-set-hash))))
        (when (eq kind :simplex)
          (check (format nil "~A: a changed session id is refused" name)
                 (refused-with :session-id (%flip-byte (cl-ton::tl-get set :session-id) 3)))
          (check (format nil "~A: a changed slot is refused" name)
                 (refused-with :slot (1+ (cl-ton::tl-get set :slot))))
          (check (format nil "~A: a changed candidate is refused" name)
                 (refused-with :candidate (%flip-byte (cl-ton::tl-get set :candidate) 10)))
          (check (format nil "~A: the same signatures in an ORDINARY set are refused" name)
                 (%vector-refused-p
                  (lambda ()
                    (cl-ton:verify-partial-block-proof
                     (%obj-with proof :steps (vector (%obj-with link :signatures
                                                               (cl-ton::tl-make "liteServer.signatureSet.ordinary"
                                                                                :validator-set-hash (cl-ton::tl-get set :validator-set-hash)
                                                                                :catchain-seqno (cl-ton::tl-get set :cc-seqno)
                                                                                :signatures sigs))))
                     known)))))
        ;; damaged bytes anywhere in the encoding: refused with a proof-error, or not decodable -- never another error
        (let ((bytes (cl-ton::tl-encode proof)) (verified 0) (refused 0) (undecodable 0) (other '()))
          (loop for i from 0 below 60
                for at = (mod (* (1+ i) 7919) (length bytes))
                do (let ((p (handler-case (cl-ton::tl-decode (%flip-byte bytes at)) (error () nil))))
                     (if (null p)
                         (incf undecodable)
                         (handler-case (progn (cl-ton:verify-partial-block-proof p known) (incf verified))
                           (cl-ton:proof-error () (incf refused))
                           (error (e) (push e other))))))
          (check (format nil "~A: 60 damaged encodings -- refused or not decodable, never another kind of error, at most 3 untouched by the damage (~D refused, ~D undecodable, ~D verified)"
                         name refused undecodable verified)
                 (and (null other) (<= verified 3))))))))

(defun test-real-link-vectors ()
  (format t "sync: real mainnet link vectors~%")
  (let ((files (directory (merge-pathnames "link-*.bin" (%real-vector-dir)))))
    (if (null files)
        (format t "  (no real link vectors yet in ~A: run TON_TRADER_LITE_DIAGNOSE=mainnet and add the files of its capture/ directory)~%"
                (%real-vector-dir))
        (dolist (bin files) (%check-link-vector bin)))))

;;; --- Simplex signature sets (the new consensus) ---------------------------------------------------
;;;
;;; The signed message is written out here from block::BlockSignatureSetSimplex::to_sign (crypto/block/
;;; signature-set.cpp), independently of CL-TON::SIGNATURE-MESSAGE: consensus.dataToSign(session_id,
;;; finalizeVote(candidateId(slot, sha256 of the boxed candidate))).  There is no real-node vector for it.

(defun %simplex-candidate (block-id &key (kind :ordinary))
  (if (eq kind :ordinary)
      (cl-ton::tl-make "consensus.candidateHashDataOrdinary" :block block-id
                                                             :collated-file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 7)
                                                             :parent (cl-ton::tl-make "consensus.candidateWithoutParents"))
      (cl-ton::tl-make "consensus.candidateHashDataEmpty" :block block-id
                                                          :parent (cl-ton::tl-make "consensus.candidateId" :slot 11
                                                                                   :hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 9)))))

(defun %simplex-message (session slot candidate-octets &key (vote "consensus.simplex.finalizeVote"))
  (cl-ton::tl-encode
   (cl-ton::tl-make "consensus.dataToSign" :session-id session
                    :data (cl-ton::tl-encode
                           (cl-ton::tl-make vote :id (cl-ton::tl-make "consensus.candidateId" :slot slot :hash (cl-ton::sha256 candidate-octets)))))))

(defun %simplex-set (signers &key (block-id (%block-id)) (candidate-block block-id) (kind :ordinary)
                               (slot 42) (session-fill 5) (signed-slot slot) (signed-session-fill session-fill)
                               candidate-octets (vote "consensus.simplex.finalizeVote"))
  (let* ((session (make-array 32 :element-type '(unsigned-byte 8) :initial-element session-fill))
         (signed-session (make-array 32 :element-type '(unsigned-byte 8) :initial-element signed-session-fill))
         (candidate (or candidate-octets (cl-ton::tl-encode (%simplex-candidate candidate-block :kind kind))))
         (message (%simplex-message signed-session signed-slot candidate :vote vote)))
    (cl-ton::tl-make "liteServer.signatureSet.simplex" :cc-seqno 0 :validator-set-hash 0
                     :signatures (coerce (mapcar (lambda (kp) (%sig-entry kp (cl-ton::sign-octets kp message))) signers) 'vector)
                     :session-id session :slot slot :candidate candidate)))

(defun test-simplex-signatures ()
  (format t "sync: Simplex signature sets~%")
  (let* ((k (mapcar #'%vkey '(0 1 2 3)))
         (id (%block-id))
         (vset3 (cl-ton:parse-validator-set (%vset-cell (subseq k 0 3) '(1 1 1))))
         (three (subseq k 0 3)))
    (check "a Simplex set signed by every validator over this block passes with their weight"
           (= 3 (cl-ton:check-block-signatures vset3 id (%simplex-set three))))
    (check "...also for an empty-block candidate, and 3 of 4 equal validators is above two thirds"
           (and (= 3 (cl-ton:check-block-signatures vset3 id (%simplex-set three :kind :empty)))
                (= 3 (cl-ton:check-block-signatures (cl-ton:parse-validator-set (%vset-cell k '(1 1 1 1))) id (%simplex-set three)))))
    (check "two of three is not above two thirds"
           (%signals cl-ton:proof-error (cl-ton:check-block-signatures vset3 id (%simplex-set (subseq k 0 2)))))
    (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
      (refuses "signatures over the ORDINARY message (a block id) in a Simplex set"
               (let ((ord (%sigset id three)))
                 (cl-ton:check-block-signatures vset3 id
                                                (%obj-with (%simplex-set three) :signatures (cl-ton::tl-get ord :signatures)))))
      (refuses "Simplex signatures in an ordinary set"
               (cl-ton:check-block-signatures vset3 id
                                              (%obj-with (%sigset id three) :signatures (cl-ton::tl-get (%simplex-set three) :signatures))))
      (refuses "a candidate for another block than the one being proved"
               (cl-ton:check-block-signatures vset3 id (%simplex-set three :candidate-block (%block-id 9))))
      (refuses "a candidate that names this block's seqno but other hashes"
               (cl-ton:check-block-signatures
                vset3 id (%simplex-set three :candidate-block (cl-ton::tl-block-id-ext :workchain -1 :shard (- (expt 2 63)) :seqno 1
                                                                                        :root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 77)
                                                                                        :file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 2)))))
      (refuses "signatures made for another slot"
               (cl-ton:check-block-signatures vset3 id (%simplex-set three :signed-slot 43)))
      (refuses "signatures made for another session"
               (cl-ton:check-block-signatures vset3 id (%simplex-set three :signed-session-fill 6)))
      (refuses "a notarize vote (the first round) presented as the final one"
               (cl-ton:check-block-signatures vset3 id (%simplex-set three :vote "consensus.simplex.notarizeVote")))
      (refuses "a candidate that does not parse"
               (cl-ton:check-block-signatures vset3 id (%simplex-set three :candidate-octets (coerce (loop repeat 30 collect (%srnd 256)) '(vector (unsigned-byte 8))))))
      (refuses "a candidate with trailing bytes (not canonical)"
               (cl-ton:check-block-signatures
                vset3 id (let ((c (cl-ton::tl-encode (%simplex-candidate id))))
                           (%simplex-set three :candidate-octets (concatenate '(vector (unsigned-byte 8)) c (vector 0 0 0 0))))))
      (refuses "a candidate of another TL type"
               (cl-ton:check-block-signatures
                vset3 id (%simplex-set three :candidate-octets (cl-ton::tl-encode (cl-ton::tl-make "ton.blockId" :root-cell-hash (cl-ton::tl-get id :root-hash)
                                                                                                   :file-hash (cl-ton::tl-get id :file-hash))))))
      (refuses "a session id of the wrong length"
               (cl-ton:check-block-signatures vset3 id (%obj-with (%simplex-set three) :session-id (make-array 31 :element-type '(unsigned-byte 8) :initial-element 5))))
      (refuses "the slot of the set changed after signing"
               (cl-ton:check-block-signatures vset3 id (%obj-with (%simplex-set three) :slot 43)))
      (refuses "a signer outside the set"
               (cl-ton:check-block-signatures vset3 id (%simplex-set (list (first k) (second k) (third k) (fourth k)))))
      (refuses "a signer twice"
               (cl-ton:check-block-signatures vset3 id (%simplex-set (list (first k) (first k) (second k) (third k))))))
    (check "the catchain seqno of a Simplex set is its cc_seqno field (header binding)"
           (let ((info (list :catchain-seqno 7 :validator-list-hash 0)))
             (and (%signals cl-ton:proof-error (cl-ton:check-validator-set-binding vset3 (%obj-with (%simplex-set three) :cc-seqno 8) info nil))
                  (let ((*verify-validator-set-hash* nil))
                    (cl-ton:check-validator-set-binding vset3 (%obj-with (%simplex-set three) :cc-seqno 7) info nil)
                    t))))))

(defun %obj-with (obj &rest changes)
  (let ((fields (copy-list (cl-ton::tl-obj-fields obj))))
    (loop for (key value) on changes by #'cddr do (setf (getf fields key) value))
    (apply #'cl-ton::tl-make (cl-ton::tl-obj-name obj) fields)))

(defun test-block-links ()
  (format t "sync: from the zero state, through a verified link, to a verified account~%")
  (if (not (%libs-available-p))
      (skip-missing "block link verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((w (%seed-wallet fc)) (addr (cl-ton:wallet-address w)))
           (cl-ton::fakechain-advance fc 3)
           (let* ((zero (%zero-block-id fc))
                  (blk (cl-ton::fc-head fc))
                  (proof (cl-ton::tl-decode
                          (cl-ton::fc-answer-block-proof
                           fc (cl-ton::tl-make "liteServer.getBlockProof" :mode 0 :known-block zero))))
                  (result (cl-ton:verify-partial-block-proof proof zero))
                  (link (aref (cl-ton::tl-get proof :steps) 0)))
             (check "the zero state's block proof verifies: one link, ending at the head, marked complete"
                    (and (= 1 (getf result :steps)) (getf result :complete)
                         (= (cl-ton::tl-get (getf result :to) :seqno) (cl-ton::fc-head-seqno fc))
                         (equalp (getf result :state-hash) (cl-ton:node-hash (cl-ton::fc-block-mc-state blk)))))
             (check "...a proof that is already at the trusted block has no links and returns it unchanged"
                    (let ((r (cl-ton:verify-partial-block-proof
                              (cl-ton::tl-make "liteServer.partialBlockProof" :complete t :from (getf result :to)
                                                                              :to (getf result :to) :steps (vector))
                              (getf result :to) :trusted-state-hash (getf result :state-hash))))
                      (and (zerop (getf r :steps)) (getf r :complete))))
             (let* ((trusted (getf result :to))
                    (answer (%served-answer fc blk addr))
                    (verified (cl-ton:verify-account-state answer addr trusted)))
               (check "end to end: the block reached by the verified chain is trusted for an account proof"
                      (getf verified :exists)))
             (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
               (flet ((with-link (&rest changes) (%obj-with proof :steps (vector (apply #'%obj-with link changes))))
                      (sigs (&rest signature-entries)
                        (cl-ton::tl-make "liteServer.signatureSet.ordinary" :validator-set-hash 0 :catchain-seqno 0
                                         :signatures (coerce signature-entries 'vector))))
                 (refuses "starting from a block that is not the one the proof is from"
                          (cl-ton:verify-partial-block-proof proof (%obj-with zero :root-hash (%flip-octet (cl-ton::tl-get zero :root-hash) 0))))
                 (refuses "a link that starts at another block than the trusted one"
                          (cl-ton:verify-partial-block-proof
                           (with-link :from (%obj-with zero :seqno 5)) zero))
                 (refuses "a link that does not move forward"
                          (cl-ton:verify-partial-block-proof
                           (%obj-with (with-link :to (%obj-with (cl-ton::tl-get link :to) :seqno 0))
                                      :to (%obj-with (cl-ton::tl-get link :to) :seqno 0))
                           zero))
                 (refuses "a link to a block in a basechain shard"
                          (cl-ton:verify-partial-block-proof (with-link :to (%obj-with (cl-ton::tl-get link :to) :workchain 0)) zero))
                 (refuses "a link whose destination id is not the block the header proof proves"
                          (cl-ton:verify-partial-block-proof
                           (%obj-with (with-link :to (%obj-with (cl-ton::tl-get link :to) :root-hash (%flip-octet (cl-ton::tl-get (cl-ton::tl-get link :to) :root-hash) 2)))
                                      :to (%obj-with (cl-ton::tl-get link :to) :root-hash (%flip-octet (cl-ton::tl-get (cl-ton::tl-get link :to) :root-hash) 2)))
                           zero))
                 (refuses "a header proof of a different block"
                          (progn (cl-ton::fakechain-advance fc 2)
                                 (cl-ton:verify-partial-block-proof
                                  (with-link :dest-proof (cl-ton::tl-get (aref (cl-ton::tl-get (cl-ton::tl-decode
                                                                                   (cl-ton::fc-answer-block-proof fc (cl-ton::tl-make "liteServer.getBlockProof" :mode 0 :known-block zero)))
                                                                                  :steps) 0)
                                                                          :dest-proof))
                                  zero)))
                 (refuses "the config proof and header proof swapped"
                          (cl-ton:verify-partial-block-proof
                           (with-link :dest-proof (cl-ton::tl-get link :config-proof) :config-proof (cl-ton::tl-get link :dest-proof)) zero))
                 (refuses "to_key_block claimed for a block that is not a key block"
                          (cl-ton:verify-partial-block-proof (with-link :to-key-block (not (cl-ton::tl-get link :to-key-block))) zero))
                 (refuses "no signatures" (cl-ton:verify-partial-block-proof (with-link :signatures (sigs)) zero))
                 (let ((sig (aref (cl-ton::tl-get (cl-ton::tl-get link :signatures) :signatures) 0)))
                   (refuses "the same genuine signature twice"
                            (cl-ton:verify-partial-block-proof (with-link :signatures (sigs sig sig)) zero))
                   (refuses "a signature by some other key"
                            (let ((other (%vkey 7)) (to (cl-ton::tl-get link :to)))
                              (cl-ton:verify-partial-block-proof
                               (with-link :signatures (sigs (%sig-entry other (%sign other to)))) zero)))
                   (refuses "the genuine signature with a bit flipped"
                            (cl-ton:verify-partial-block-proof
                             (with-link :signatures
                               (sigs (%sig-entry-from sig (%flip-octet (cl-ton::tl-get sig :signature) 9))))
                             zero)))
                 (refuses "the config proof of a state that is not the trusted block's"
                          (cl-ton:verify-partial-block-proof
                           (with-link :config-proof (cl-ton::fc-proof-boc (cl-ton::fc-config-proof-node (cl-ton::fc-block-mc-state blk))))
                           zero))
                 (refuses "a chain that ends somewhere else than the proof claims"
                          (cl-ton:verify-partial-block-proof (%obj-with proof :steps (vector)) zero))
                 (refuses "a backward link where a forward one is expected"
                          (cl-ton:verify-partial-block-proof
                           (%obj-with proof :steps (vector (cl-ton::tl-make "liteServer.blockLinkBack" :to-key-block nil
                                                                            :from (cl-ton::tl-get link :to) :to zero
                                                                            :dest-proof (cl-ton::tl-get link :dest-proof)
                                                                            :proof (cl-ton::tl-get link :dest-proof)
                                                                            :state-proof (cl-ton::tl-get link :dest-proof))))
                           zero))
                 (refuses "garbage instead of the header proof"
                          (cl-ton:verify-partial-block-proof
                           (with-link :dest-proof (coerce (loop repeat 50 collect (%srnd 256)) '(vector (unsigned-byte 8)))) zero))
                 (refuses "a forward link out of a trusted block that is not a key block (its config proof cannot match)"
                          (cl-ton:verify-partial-block-proof (with-link :from (getf result :to)) (getf result :to)))))))))))

(defun %sig-entry-from (entry signature)
  (cl-ton::tl-make "liteServer.signature" :node-id-short (cl-ton::tl-get entry :node-id-short) :signature signature))

(defun test-block-link-fuzz ()
  (format t "sync: corrupted block proofs are only ever refused with a proof-error~%")
  (if (not (%libs-available-p))
      (skip-missing "block link fuzz (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (%seed-wallet fc)
         (cl-ton::fakechain-advance fc 2)
         (let* ((zero (%zero-block-id fc))
                (proof (cl-ton::tl-decode (cl-ton::fc-answer-block-proof
                                           fc (cl-ton::tl-make "liteServer.getBlockProof" :mode 0 :known-block zero))))
                (link (aref (cl-ton::tl-get proof :steps) 0))
                (accepted 0) (refused 0) (other '()))
           (flet ((try (altered-link)
                    (handler-case (progn (cl-ton:verify-partial-block-proof
                                          (%obj-with proof :steps (vector altered-link)) zero)
                                         (incf accepted))
                      (cl-ton:proof-error () (incf refused))
                      (error (e) (push (princ-to-string e) other)))))
             (dolist (field '(:dest-proof :config-proof))
               (let ((octets (cl-ton::tl-get link field)))
                 (dotimes (i 120)
                   (let ((v (copy-seq octets)))
                     (dotimes (k (1+ (%srnd 3))) (setf (aref v (%srnd (length v))) (%srnd 256)))
                     (try (%obj-with link field v))))
                 (dotimes (i 20) (try (%obj-with link field (subseq octets 0 (%srnd (length octets))))))))
             (let* ((sig (aref (cl-ton::tl-get (cl-ton::tl-get link :signatures) :signatures) 0))
                    (octets (cl-ton::tl-get sig :signature)))
               (dotimes (i 120)
                 (let ((v (copy-seq octets))) (setf (aref v (%srnd 64)) (%srnd 256))
                   (unless (equalp v octets)
                     (try (%obj-with link :signatures
                                     (cl-ton::tl-make "liteServer.signatureSet.ordinary" :validator-set-hash 0 :catchain-seqno 0
                                                      :signatures (vector (%sig-entry-from sig v)))))))))
             (check (format nil "~D corrupted block links: ~D refused, ~D still verified, ~D failed with another kind of error ~S"
                            (+ refused accepted (length other)) refused accepted (length other) (subseq other 0 (min 3 (length other))))
                    (null other))
             (check "...and none of them verified unless the corruption changed nothing that matters"
                    (< accepted 5))))))))

(defun %catchain-cell (tag &key (flags 0) shuffle (values '(25 26 27 8)))
  (let ((b (cl-ton:store-uint (cl-ton:begin-cell) tag 8)))
    (when (= tag #xc2)
      (setf b (cl-ton:store-uint (cl-ton:store-uint b flags 7) (if shuffle 1 0) 1)))
    (dolist (v values) (setf b (cl-ton:store-uint b v 32)))
    (cl-ton:end-cell b)))

(defun test-catchain-config ()
  (format t "sync: the catchain configuration (parameter 28)~%")
  (check "catchain_config#c1: four lifetimes/counts, no shuffle"
         (equal (cl-ton:parse-catchain-config (%catchain-cell #xc1))
                '(:shuffle-mc-validators nil :mc-catchain-lifetime 25 :shard-catchain-lifetime 26
                  :shard-validators-lifetime 27 :shard-validators-num 8)))
  (check "catchain_config_new#c2: the shuffle flag in front, both settings"
         (and (getf (cl-ton:parse-catchain-config (%catchain-cell #xc2 :shuffle t)) :shuffle-mc-validators)
              (not (getf (cl-ton:parse-catchain-config (%catchain-cell #xc2 :shuffle nil)) :shuffle-mc-validators))
              (= 8 (getf (cl-ton:parse-catchain-config (%catchain-cell #xc2 :shuffle t)) :shard-validators-num))))
  (check "an absent parameter means the defaults: no shuffle"
         (not (getf (cl-ton:parse-catchain-config nil) :shuffle-mc-validators)))
  (check "unknown constructors and non-zero flags are refused"
         (and (%signals cl-ton:proof-error (cl-ton:parse-catchain-config (%catchain-cell #xc3)))
              (%signals cl-ton:proof-error (cl-ton:parse-catchain-config (%catchain-cell #xc2 :flags 1)))
              (%signals cl-ton:proof-error (cl-ton:parse-catchain-config (%catchain-cell #xc1 :values '(1 2))))))
  (if (not (%libs-available-p))
      (skip-missing "the fakechain's parameter 28 (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (let* ((blk (cl-ton::fc-head fc))
                (cfg28 (cl-ton:config-param (cl-ton:masterchain-config-root (cl-ton::fc-block-mc-state blk)) 28)))
           (check "the fakechain's own parameter 28 (tonlib accepts it) parses: 25/25/25 and 8, no shuffle"
                  (equal (cl-ton:parse-catchain-config cfg28)
                         '(:shuffle-mc-validators nil :mc-catchain-lifetime 25 :shard-catchain-lifetime 25
                           :shard-validators-lifetime 25 :shard-validators-num 8))))))))

(defun %config-answer (fc blk &key params)
  "A liteServer.configInfo for BLK as a liteserver would send: everything, or only PARAMS."
  (cl-ton::tl-make "liteServer.configInfo" :mode 0 :id (cl-ton::fc-mc-id blk)
                   :state-proof (cl-ton::fc-proof-boc (cl-ton::fc-header-proof-node (cl-ton::fc-block-mc-block blk)))
                   :config-proof (cl-ton::fc-proof-boc
                                  (if params
                                      (cl-ton::fc-config-proof-node (cl-ton::fc-block-mc-state blk) params)
                                      (cl-ton::fc-config-proof-node (cl-ton::fc-block-mc-state blk) :all)))))

(defun test-config-answers ()
  (format t "sync: configuration answers, from a trusted block hash down~%")
  (if (not (%libs-available-p))
      (skip-missing "configuration answer verification (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (%seed-wallet fc)
         (cl-ton::fakechain-advance fc 2)
         (let* ((blk (cl-ton::fc-head fc)) (trusted (cl-ton::fc-mc-id blk))
                (genuine (cl-ton::tl-decode (cl-ton::fc-answer-config-all fc (cl-ton::tl-make "liteServer.getConfigAll" :mode 0 :id trusted))))
                (all (cl-ton:verify-config-info genuine trusted :all t :params '(34 99)))
                (partial (%config-answer fc blk :params '(28 34))))
           (check "getConfigAll verifies with every parameter checked visible; parameter 34 is the validator set"
                  (and (cl-ton:cell-p (cdr (assoc 34 (getf all :params))))
                       (= 1 (length (cl-ton:validator-set-members (cl-ton:parse-validator-set (cdr (assoc 34 (getf all :params)))))))))
           (check "...an absent parameter (99) is proved absent, not an error" (null (cdr (assoc 99 (getf all :params)))))
           (check "...and the state hash it ends at is the masterchain state's"
                  (equalp (getf all :state-hash) (cl-ton:node-hash (cl-ton::fc-block-mc-state blk))))
           (check "a partial proof verifies for the parameters it reveals (28 and 34)"
                  (let ((r (cl-ton:verify-config-info partial trusted :params '(28 34))))
                    (and (cdr (assoc 28 (getf r :params))) (cdr (assoc 34 (getf r :params))))))
           (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
             (refuses "a partial proof when the whole configuration is demanded (pruned cells)"
                      (cl-ton:verify-config-info partial trusted :all t))
             (refuses "a parameter the partial proof does not reveal (31)"
                      (cl-ton:verify-config-info partial trusted :params '(31)))
             (refuses "a different trusted block" (cl-ton:verify-config-info genuine (%id-with trusted :seqno 1)))
             (refuses "a different trusted root hash"
                      (cl-ton:verify-config-info genuine (%id-with trusted :root-hash (%flip-octet (cl-ton::tl-get trusted :root-hash) 0))))
             (refuses "an answer claiming another block than the one it proves"
                      (cl-ton:verify-config-info
                       (%obj-with genuine :id (%id-with trusted :root-hash (%flip-octet (cl-ton::tl-get trusted :root-hash) 1)))
                       (%id-with trusted :root-hash (%flip-octet (cl-ton::tl-get trusted :root-hash) 1))))
             (refuses "the two proofs swapped"
                      (cl-ton:verify-config-info (%obj-with genuine :state-proof (cl-ton::tl-get genuine :config-proof)
                                                                    :config-proof (cl-ton::tl-get genuine :state-proof))
                                                 trusted))
             (refuses "the config proof of another block"
                      (progn (cl-ton::fakechain-advance fc 2)
                             (cl-ton:verify-config-info
                              (%obj-with genuine :config-proof (cl-ton::tl-get (%config-answer fc (cl-ton::fc-head fc)) :config-proof))
                              trusted)))
             (refuses "garbage for the config proof"
                      (cl-ton:verify-config-info
                       (%obj-with genuine :config-proof (coerce (loop repeat 50 collect (%srnd 256)) '(vector (unsigned-byte 8))))
                       trusted))
             (refuses "a truncated config proof"
                      (cl-ton:verify-config-info
                       (%obj-with genuine :config-proof (subseq (cl-ton::tl-get genuine :config-proof) 0
                                                               (floor (length (cl-ton::tl-get genuine :config-proof)) 2)))
                       trusted))
             (refuses "one flipped byte in the config proof"
                      (cl-ton:verify-config-info
                       (%obj-with genuine :config-proof (%flip-octet (cl-ton::tl-get genuine :config-proof)
                                                                    (floor (length (cl-ton::tl-get genuine :config-proof)) 2)))
                       trusted))
             (refuses "a config proof whose validator-set parameter was swapped for another (consistently rebuilt)"
                      (let* ((roots (cl-ton:parse-boc (cl-ton::tl-get genuine :config-proof))))
                        (multiple-value-bind (forged did) (%forge-pruned (first roots))
                          (declare (ignore did))
                          (cl-ton:verify-config-info (%obj-with genuine :config-proof (cl-ton::fc-proof-boc (if (cl-ton:cell-p forged) forged (first roots))))
                                                     trusted))))))))))

(defun test-config-fuzz ()
  (format t "sync: corrupted configuration answers are only ever refused with a proof-error~%")
  (if (not (%libs-available-p))
      (skip-missing "configuration fuzz (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 2)
         (let* ((blk (cl-ton::fc-head fc)) (trusted (cl-ton::fc-mc-id blk))
                (genuine (%config-answer fc blk)) (refused 0) (accepted 0) (other '()))
           (dolist (field '(:state-proof :config-proof))
             (let ((octets (cl-ton::tl-get genuine field)))
               (dotimes (i 150)
                 (let ((v (copy-seq octets)))
                   (dotimes (k (1+ (%srnd 3))) (setf (aref v (%srnd (length v))) (%srnd 256)))
                   (handler-case (progn (cl-ton:verify-config-info (%obj-with genuine field v) trusted :all t) (incf accepted))
                     (cl-ton:proof-error () (incf refused))
                     (error (e) (push (princ-to-string e) other)))))))
           (check (format nil "300 corrupted answers: ~D refused, ~D still verified, ~D failed with another kind of error ~S"
                          refused accepted (length other) (subseq other 0 (min 3 (length other))))
                  (null other))
           (check "...and none of them verified" (< accepted 5)))))))

;;; --- the validator-set hash and the masterchain order ---------------------------------

(defun %zero32 () (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))

(defun test-validator-set-hash ()
  (format t "sync: the validator-set hash, the masterchain shuffle and their binding to a block~%")
  ;; the expected values below come from an independent Python rendering of the node's source
  (let ((g (cl-ton:make-validator-prng :cc-seqno 0)))
    (check "the PRNG's first ten u64 (SHA-512 of the big-endian descriptor, seed incremented per hash)"
           (equal (loop repeat 10 collect (cl-ton:prng-next-ulong g))
                  '(6186953295200455061 9716249430906648876 893850564141714240 16362499097668570104
                    7550721807492789767 8027788155046975774 2198044665159296191 15889925754150310949
                    2854201576873883948 3908958851740847745))))
  (check "...for another catchain seqno"
         (let ((g (cl-ton:make-validator-prng :cc-seqno 7)))
           (equal (loop repeat 3 collect (cl-ton:prng-next-ulong g))
                  '(7740061943499001564 8939104149805571666 8341264594806853058))))
  (check "the shuffle of 10 at seqno 5, of 7 at 123456, and the head of 100 at a seqno above 2^31"
         (and (equalp (cl-ton:shuffle-masterchain-validators (loop for i below 10 collect i) 5)
                      #(7 3 1 9 8 5 2 0 6 4))
              (equalp (cl-ton:shuffle-masterchain-validators (loop for i below 7 collect i) 123456)
                      #(5 6 4 3 1 0 2))
              (equalp (subseq (cl-ton:shuffle-masterchain-validators (loop for i below 100 collect i) 4000000000) 0 12)
                      #(11 27 46 90 57 80 6 38 97 53 98 28))))
  (check "the CRC32C check value (\"123456789\")"
         (= #xE3069283 (cl-ton:crc32c (map '(vector (unsigned-byte 8)) #'char-code "123456789"))))
  (let ((nodes (loop for i below 3 collect (list (make-array 32 :element-type '(unsigned-byte 8) :initial-element i)
                                                 (+ 10 i)
                                                 (make-array 32 :element-type '(unsigned-byte 8) :initial-element (+ #xa0 i))))))
    (check "the set hash of three validators with adnl addresses at seqno 9, and of the empty set"
           (and (= 1508102348 (cl-ton:compute-validator-set-hash 9 nodes))
                (= 3900357565 (cl-ton:compute-validator-set-hash 0 '())))))
  (check "the fakechain's validator set hashes to the value real tonlib checks (1234420764)"
         (= 1234420764
            (cl-ton:compute-validator-set-hash
             0 (list (list (cl-ton::keypair-public (cl-ton::seed->keypair cl-ton::+fc-validator-seed+)) 1 (%zero32))))))
  ;; the binding, on a ten-validator set
  (let* ((kps (mapcar #'%vkey (loop for i below 10 collect i)))
         (weights (loop for i from 1 to 10 collect i))
         (vset (cl-ton::parse-validator-set (%vset-cell kps weights)))
         (nodes (loop for kp in kps for w in weights collect (list (cl-ton::keypair-public kp) w (%zero32))))
         (shuffled (map 'list (lambda (i) (nth i nodes)) '(7 3 1 9 8 5 2 0 6 4)))
         (plain (cl-ton::hashmap-cell (list (cons 28 (lambda (b) (cl-ton:store-ref b (%catchain-cell #xc1))))) 32))
         (shuffling (cl-ton::hashmap-cell (list (cons 28 (lambda (b) (cl-ton:store-ref b (%catchain-cell #xc2 :shuffle t))))) 32))
         (without (cl-ton::hashmap-cell (list (cons 29 (lambda (b) (cl-ton:store-ref b (%catchain-cell #xc1))))) 32)))
    (flet ((info (cc hash) (list :catchain-seqno cc :validator-list-hash hash))
           (sigset (cc hash) (cl-ton::tl-make "liteServer.signatureSet.ordinary" :validator-set-hash hash
                                                                                  :catchain-seqno cc :signatures (vector))))
      (let ((h-plain (cl-ton:compute-validator-set-hash 5 nodes))
            (h-shuffled (cl-ton:compute-validator-set-hash 5 shuffled)))
        (check "the masterchain hash of a shuffled set is the hash of the permuted list; unshuffled, of the list as is"
               (and (= h-shuffled (cl-ton:masterchain-validator-set-hash vset 5 t))
                    (= h-plain (cl-ton:masterchain-validator-set-hash vset 5 nil))
                    (/= h-plain h-shuffled)))
        (check "a block, a signature set and a configuration that agree pass (shuffling on, shuffling off, no parameter 28)"
               (and (null (cl-ton:check-validator-set-binding vset (sigset 5 h-shuffled) (info 5 h-shuffled) shuffling))
                    (null (cl-ton:check-validator-set-binding vset (sigset 5 h-plain) (info 5 h-plain) plain))
                    (null (cl-ton:check-validator-set-binding vset (sigset 5 h-plain) (info 5 h-plain) without))))
        (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
          (refuses "a header hash that is the unshuffled one when the configuration shuffles"
                   (cl-ton:check-validator-set-binding vset (sigset 5 h-plain) (info 5 h-plain) shuffling))
          (refuses "a header hash that is the shuffled one when the configuration does not shuffle"
                   (cl-ton:check-validator-set-binding vset (sigset 5 h-shuffled) (info 5 h-shuffled) plain))
          (refuses "a header hash that is the shuffled one when parameter 28 is absent"
                   (cl-ton:check-validator-set-binding vset (sigset 5 h-shuffled) (info 5 h-shuffled) without))
          (refuses "a signature set for another catchain seqno than the header's"
                   (cl-ton:check-validator-set-binding vset (sigset 6 h-shuffled) (info 5 h-shuffled) shuffling))
          (refuses "a signature set with another validator set hash than the header's"
                   (cl-ton:check-validator-set-binding vset (sigset 5 (1+ h-shuffled)) (info 5 h-shuffled) shuffling))
          (refuses "a header at another catchain seqno than the hash was made for"
                   (cl-ton:check-validator-set-binding vset (sigset 6 h-shuffled) (info 6 h-shuffled) shuffling)))
        (check "with recomputation switched off the two stated hashes must still agree, the recomputation is skipped"
               (let ((cl-ton:*verify-validator-set-hash* nil))
                 (and (null (cl-ton:check-validator-set-binding vset (sigset 5 777) (info 5 777) shuffling))
                      (%signals cl-ton:proof-error
                        (cl-ton:check-validator-set-binding vset (sigset 5 778) (info 5 777) shuffling))))))))
  ;; the same on a real link of the fakechain
  (if (not (%libs-available-p))
      (skip-missing "link binding (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (cl-ton::fakechain-advance fc 3)
         (let* ((zero (%zero-block-id fc))
                (proof (cl-ton::tl-decode
                        (cl-ton::fc-answer-block-proof
                         fc (cl-ton::tl-make "liteServer.getBlockProof" :mode 0 :known-block zero))))
                (link (aref (cl-ton::tl-get proof :steps) 0))
                (sigs (cl-ton::tl-get link :signatures)))
           (flet ((with-sigs (&rest changes)
                    (%obj-with proof :steps (vector (%obj-with link :signatures (apply #'%obj-with sigs changes))))))
             (check "the fakechain's link verifies with the hash recomputed from its configuration"
                    (getf (cl-ton:verify-partial-block-proof proof zero) :complete))
             (check "...and with the recomputation off"
                    (let ((cl-ton:*verify-validator-set-hash* nil))
                      (getf (cl-ton:verify-partial-block-proof proof zero) :complete)))
             (check "a link whose signature set names another catchain seqno is refused"
                    (%signals cl-ton:proof-error
                      (cl-ton:verify-partial-block-proof (with-sigs :catchain-seqno 1) zero)))
             (check "a link whose signature set carries another validator set hash is refused"
                    (%signals cl-ton:proof-error
                      (cl-ton:verify-partial-block-proof
                       (with-sigs :validator-set-hash (1+ (cl-ton::tl-get sigs :validator-set-hash))) zero)))))))))


;;; --- forward links out of a NON-ZERO key block (the init_block path) ------------------------------
;;;
;;; The fakechain has no key block but the zero state, so the key block is built here: a masterchain Block
;;; whose McBlockExtra carries key_block = 1 and the fakechain's own configuration, revealed in a proof
;;; the way a node reveals it in a forward link (extract_from_key_block reads it from the block itself,
;;; no state hash of the block is involved).

(defun %key-block (head &key (seqno 1) (key t) (utime 1))
  "A masterchain Block cell of SEQNO that carries the configuration of HEAD's state in its McBlockExtra
(KEY_BLOCK set when KEY), and its blockIdExt."
  (let* ((config (cl-ton:masterchain-config-root (cl-ton::fc-block-mc-state head)))
         (custom (cl-ton:end-cell
                  (cl-ton:store-ref
                   (cl-ton:store-ref
                    (cl-ton::%store-hash
                     (cl-ton::%fc-coins0 (cl-ton:store-bit (cl-ton:store-bit (cl-ton:store-bit
                                                                              (cl-ton:store-uint (cl-ton:begin-cell) #xcca5 16)
                                                                              (if key 1 0)) 0) 0))
                     (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))
                    (cl-ton:end-cell (cl-ton:store-bit (cl-ton:store-bit (cl-ton:store-bit (cl-ton:begin-cell) 0) 0) 0)))
                   config)))
         (head-block (cl-ton::fc-block-mc-block head))
         (info (cl-ton::%block-info-cell :not-master nil :seqno seqno :workchain -1 :shard cl-ton::+mc-shard+
                                         :utime utime :start-lt 1 :end-lt 2 :prev-ref (list 0 0 (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)
                                                                                           (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))))
         (blk (cl-ton:end-cell
                 (cl-ton:store-ref
                  (cl-ton:store-ref
                   (cl-ton:store-ref
                    (cl-ton:store-ref (cl-ton:store-int (cl-ton:store-uint (cl-ton:begin-cell) #x11ef55aa 32)
                                                        cl-ton::+fake-global-id+ 32)
                                      info)
                    (cl-ton::%value-flow-cell))
                   (svref (cl-ton:cell-refs head-block) 2))
                  (cl-ton::%block-extra-cell utime custom)))))
    (values blk
            (cl-ton::tl-block-id-ext :workchain -1 :shard (- (expt 2 63)) :seqno seqno
                                     :root-hash (cl-ton:node-hash blk)
                                     :file-hash (cl-ton::%file-hash blk)))))

(defun %key-block-config-proof (block)
  "BLOCK revealed as a node reveals a key block's configuration: the block cell, its BlockExtra, the
McBlockExtra and the configuration parameters a node reveals in a forward link (35, 34 and 28: the next set, 36, stays pruned); the rest pruned."
  (let* ((visible (make-hash-table :test #'equalp))
         (extra (svref (cl-ton:cell-refs block) 3))
         (custom (svref (cl-ton:cell-refs extra) 3))
         (config (svref (cl-ton:cell-refs custom) (1- (length (cl-ton:cell-refs custom))))))
    (flet ((show (c) (setf (gethash (cl-ton:node-hash c) visible) t)))
      (show block) (show extra) (show custom)
      (dolist (key '(35 34 28))
        (let ((path (cl-ton::dict-path-cells config key 32)))
          (mapc #'show path)
          (let ((leaf (car (last path))))
            (when (plusp (length (cl-ton:cell-refs leaf)))
              (mapc #'show (cl-ton::collect-nodes (cl-ton::first-ref-cell leaf))))))))
    (cl-ton::fc-proof-boc (cl-ton::prune-tree block (lambda (c) (gethash (cl-ton:node-hash c) visible))))))

(defun test-key-block-links ()
  (format t "sync: forward links out of a non-zero key block (init_block)~%")
  (if (not (%libs-available-p))
      (skip-missing "key block links (emulator shared library)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore tl proxy cfg))
         (%seed-wallet fc)
         (cl-ton::fakechain-advance fc 3)
         (let ((head (cl-ton::fc-head fc)))
           (multiple-value-bind (kblock kid) (%key-block head)
             (let* ((link (%obj-with (cl-ton::fc-forward-link fc kid head)
                                     :config-proof (%key-block-config-proof kblock)))
                    (proof (cl-ton::tl-make "liteServer.partialBlockProof" :complete t :from kid
                                            :to (cl-ton::fc-mc-id head) :steps (vector link))))
               (check "a forward link out of a key block verifies from its id alone (no state hash)"
                      (let ((r (cl-ton:verify-partial-block-proof proof kid)))
                        (and (getf r :complete) (= 1 (getf r :steps))
                             (= (cl-ton::tl-get (getf r :to) :seqno) (cl-ton::tl-get (cl-ton::fc-mc-id head) :seqno)))))
               (check "a node's forward link: the destination header proof shows only BlockInfo (state_update pruned)"
                      (let* ((hb (cl-ton::fc-block-mc-block head))
                             (vis (make-hash-table :test #'equalp)))
                        (setf (gethash (cl-ton:node-hash hb) vis) t)
                        (dolist (n (cl-ton::collect-nodes (svref (cl-ton:cell-refs hb) 0)))
                          (setf (gethash (cl-ton:node-hash n) vis) t))
                        (let* ((thin (cl-ton::fc-proof-boc (cl-ton::prune-tree hb (lambda (c) (gethash (cl-ton:node-hash c) vis)))))
                               (r (cl-ton:verify-partial-block-proof
                                   (%obj-with proof :steps (vector (%obj-with link :dest-proof thin))) kid)))
                          (and (getf r :complete) (null (getf r :state-hash))
                               (= (cl-ton::tl-get (getf r :to) :seqno) (cl-ton::tl-get (cl-ton::fc-mc-id head) :seqno))))))
               (check "...and a wrong state hash passed along changes nothing"
                      (getf (cl-ton:verify-partial-block-proof proof kid :trusted-state-hash (%flip-octet (cl-ton::tl-get kid :root-hash) 0))
                            :complete))
               (macrolet ((refuses (what form) `(check ,what (%signals cl-ton:proof-error ,form))))
                 (refuses "a config proof of another block than the trusted key block"
                          (multiple-value-bind (other) (%key-block head :utime 2)
                            (cl-ton:verify-partial-block-proof
                             (%obj-with proof :steps (vector (%obj-with link :config-proof (%key-block-config-proof other)))) kid)))
                 (refuses "a trusted id whose root hash is not the proved block's"
                          (let ((bad (%id-with kid :root-hash (%flip-octet (cl-ton::tl-get kid :root-hash) 3))))
                            (cl-ton:verify-partial-block-proof
                             (%obj-with proof :from bad :steps (vector (%obj-with link :from bad))) bad)))
                 (refuses "a block without the key_block flag (no configuration)"
                          (multiple-value-bind (plain pid) (%key-block head :key nil)
                            (cl-ton:verify-partial-block-proof
                             (%obj-with proof :from pid :steps (vector (%obj-with link :from pid :config-proof (%key-block-config-proof plain))))
                             pid)))
                 (refuses "a state proof (the zero state's) in place of the key block's proof"
                          (cl-ton:verify-partial-block-proof
                           (%obj-with proof :steps (vector (%obj-with link :config-proof
                                                                      (cl-ton::fc-proof-boc (cl-ton::fc-config-proof-node (cl-ton::fakechain-zero-state fc))))))
                           kid))
                 (refuses "garbage for the config proof"
                          (cl-ton:verify-partial-block-proof
                           (%obj-with proof :steps (vector (%obj-with link :config-proof (coerce (loop repeat 50 collect (%srnd 256)) '(vector (unsigned-byte 8))))))
                           kid))))))))))


;;; --- many signatures at once (ed25519-batch.lisp) --------------------------------------------------

(defun %ed-keypair ()
  (let* ((priv (ironclad:make-private-key :ed25519 :x (ironclad:random-data 32))))
    (values priv (ironclad:ed25519-key-y priv))))

(defun %ed-entry (&optional (message (ironclad:random-data 40)))
  (multiple-value-bind (priv pub) (%ed-keypair)
    (list pub message (ironclad:sign-message priv message))))

(defun %ed-damage (entry how)
  (destructuring-bind (pub message signature) entry
    (ecase how
      (:signature (let ((s (copy-seq signature))) (setf (aref s 5) (logxor 1 (aref s 5))) (list pub message s)))
      (:s-part (let ((s (copy-seq signature))) (setf (aref s 40) (logxor 4 (aref s 40))) (list pub message s)))
      (:message (let ((m (copy-seq message))) (setf (aref m 3) (logxor 1 (aref m 3))) (list pub m signature)))
      (:key (list (ironclad:ed25519-key-y (ironclad:make-private-key :ed25519 :x (ironclad:random-data 32))) message signature)))))

(defun test-ed25519-batch ()
  (format t "sync: batched Ed25519 verification, pure and in parallel~%")
  (let* ((good (loop repeat 30 collect (%ed-entry)))
         (agree 0) (checked 0))
    (check "an empty batch is valid" (null (cl-ton:ed25519-first-invalid '())))
    (check "30 valid signatures verify as one batch"
           (null (cl-ton:ed25519-first-invalid good)))
    (check "the batch check is pure: the same answer every time, no input changed"
           (let ((before (copy-tree good)))
             (and (null (cl-ton:ed25519-first-invalid good)) (null (cl-ton:ed25519-first-invalid good))
                  (equalp before good))))
    (dolist (how '(:signature :s-part :message :key))
      (let* ((position (random 30))
             (entries (loop for e in good for i from 0 collect (if (= i position) (%ed-damage e how) e))))
        (check (format nil "a ~(~A~) damaged in one of 30 is found, and it is the right one" how)
               (eql position (cl-ton:ed25519-first-invalid entries)))))
    (check "the first of several bad ones is reported (whether a bad one is not even a point or not)"
           (loop repeat 12
                 always (eql 4 (cl-ton:ed25519-first-invalid
                                (loop for e in good for i from 0
                                      collect (if (member i '(4 9 20)) (%ed-damage e (if (= i 4) :s-part :signature)) e))))))
    (check "a signature with s not below the group order is refused"
           (let* ((e (first good)) (s (copy-seq (third e))))
             (replace s (ironclad:integer-to-octets (+ crypto::+ed25519-l+ (ironclad:octets-to-integer s :start 32 :end 64 :big-endian nil))
                                                    :n-bits 256 :big-endian nil)
                      :start1 32)
             (eql 0 (cl-ton:ed25519-first-invalid (list (list (first e) (second e) s))))))
    (check "wrong lengths are refused, not signalled"
           (and (eql 0 (cl-ton:ed25519-first-invalid (list (list (subseq (first (first good)) 0 31) (second (first good)) (third (first good))))))
                (eql 0 (cl-ton:ed25519-first-invalid (list (list (first (first good)) (second (first good)) (subseq (third (first good)) 0 63)))))))
    (check "one signer signing many messages (a validator over many links) is one batch"
           (multiple-value-bind (priv pub) (%ed-keypair)
             (let ((entries (loop repeat 20 collect (let ((m (ironclad:random-data 33))) (list pub m (ironclad:sign-message priv m))))))
               (and (null (cl-ton:ed25519-first-invalid entries))
                    (eql 13 (cl-ton:ed25519-first-invalid
                             (loop for e in entries for i from 0 collect (if (= i 13) (%ed-damage e :message) e))))))))
    ;; agreement with ironclad's own verification, valid and damaged alike
    (dotimes (i 40)
      (let* ((e (%ed-entry)) (e (if (evenp i) e (%ed-damage e (nth (mod i 4) '(:signature :s-part :message :key)))))
             (alone (ironclad:verify-signature (ironclad:make-public-key :ed25519 :y (first e)) (second e) (third e)))
             (batched (null (cl-ton:ed25519-first-invalid (list e)))))
        (incf checked) (when (eq (and alone t) batched) (incf agree))))
    (check "40 single signatures, half of them damaged: batch and ironclad always agree" (= agree checked))
    (check "the multi-scalar multiplication equals the sum of ironclad scalar multiplications"
           (let* ((pts (loop repeat 9 collect (ironclad:ec-scalar-mult crypto::+ed25519-b+ (1+ (random 1000000)))))
                  (ks (loop repeat 9 collect (random (expt 2 200))))
                  (m (cl-ton::%multi-scalar-mult (coerce pts 'vector) (coerce ks 'vector)))
                  (naive (let ((acc (cl-ton::%identity-point)))
                           (loop for p in pts for k in ks do (setf acc (ironclad:ec-add acc (ironclad:ec-scalar-mult p k))))
                           acc)))
             (ironclad:ec-point-equal m naive)))
    (check "parallel-map equals mapcar, in order, on several workers"
           (equal (cl-ton:parallel-map (lambda (x) (* x x)) (loop for i below 25 collect i) :workers 4)
                  (loop for i below 25 collect (* i i))))
    (check "an error in a worker is raised by the caller"
           (%signals error (cl-ton:parallel-map (lambda (x) (if (= x 7) (error "boom") x)) (loop for i below 12 collect i) :workers 3)))
    (check "signature jobs: all valid pass; the failing link is named"
           (let* ((jobs (loop for l from 1 to 6
                              collect (cons (format nil "link ~D" l)
                                            (loop repeat 5 collect (append (%ed-entry) (list (ironclad:random-data 32)))))))
                  (bad (loop for job in jobs for l from 1
                             collect (if (= l 4)
                                         (cons (car job) (cons (append (%ed-damage (subseq (first (cdr job)) 0 3) :signature) (list (ironclad:random-data 32)))
                                                               (cdr (cdr job))))
                                         job))))
             (and (progn (let ((cl-ton:*worker-count* 3)) (cl-ton:check-signature-jobs jobs)) t)
                  (handler-case (progn (let ((cl-ton:*worker-count* 3)) (cl-ton:check-signature-jobs bad)) nil)
                    (cl-ton:proof-error (e) (search "link 4" (princ-to-string e)))))))))

(defun test-sync ()
  (test-validator-sets)
  (test-validator-set-hash)
  (test-catchain-config)
  (test-block-links)
  (test-block-link-fuzz)
  (test-key-block-links)
  (test-ed25519-batch)
  (test-config-answers)
  (test-config-fuzz))
