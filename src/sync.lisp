;;;; sync.lisp -- from a trusted masterchain block to a newer one.
;;;;
;;;; The one thing a client trusts without proof is where it starts: the zero state named in its
;;;; global config.  A liteserver then sends a chain of block links.  A FORWARD link carries the
;;;; header proof of the next block, a proof of the CONFIGURATION of the block we already trust,
;;;; and a set of validator signatures:
;;;;
;;;;   trusted block F --(config proof, checked against F's state hash)--> validator sets
;;;;   next block T    --(header proof, checked against T's root hash)---> T's state hash, time
;;;;   signatures      --(ed25519 over T's id, validators from F's config)--> weight > 2/3
;;;;
;;;; and then T is trusted too, and its state hash is what the next link's config proof is checked
;;;; against.  Nothing a liteserver says is believed beyond what this chain makes it.
;;;;
;;;; Strict by design: a signature from an unknown validator, a repeated signer or an invalid
;;;; signature rejects the whole set (it does not just not count), and a signature set type this
;;;; code does not know is refused rather than skipped.
;;;;
;;;; The signature set's catchain seqno and validator_set_hash must equal the block header's
;;;; gen_catchain_seqno and gen_validator_list_hash_short, and the hash is recomputed from the trusted
;;;; configuration (CRC32C of the set in the node's order, shuffled when parameter 28 says so), unless
;;;; *VERIFY-VALIDATOR-SET-HASH* is NIL.  This adds nothing to the cryptographic guarantee -- the
;;;; signatures are over the block id and the signers come from the trusted configuration -- it
;;;; keeps the client in step with what the node itself checks.  Not yet seen against real chain data.

(in-package :cl-ton)

;;; --- validator sets -------------------------------------------------------------------

(defstruct (validator-set (:copier nil))
  since until                           ; the unix times it is in force
  main total-weight                     ; the main validators sign masterchain blocks
  members)                              ; vector of (SHORT-ID PUBLIC-KEY WEIGHT ADNL-ADDR), the main ones, in list order

(defun %parse-validator-descr (slice)
  "validator#53 / validator_addr#73 public_key:SigPubKey weight:uint64 [adnl_addr:bits256]:
(VALUES PUBLIC-KEY WEIGHT ADNL-ADDR), the address being 32 zero octets for a validator#53, as the node
takes it."
  (multiple-value-bind (tag s) (load-uint slice 8)
    (%prove (member tag '(#x53 #x73)) "unknown validator descriptor ~X" tag)
    (multiple-value-bind (key-tag s) (load-uint s 32)
      (%prove (= key-tag #x8e81278a) "a validator key that is not ed25519 (~X)" key-tag)
      (multiple-value-bind (key s) (load-bytes s 32)
        (multiple-value-bind (weight s) (load-uint s 64)
          (values key weight (if (= tag #x73) (load-bytes s 32) (make-array 32 :element-type '(unsigned-byte 8)
                                                                               :initial-element 0))))))))

(define-proof-function parse-validator-set (cell)
  "A config parameter 32..37 cell: validators#11 / validators_ext#12 utime_since utime_until
total:(## 16) main:(## 16) [total_weight:uint64] list.  The list holds TOTAL validators, keys 0..TOTAL-1,
all of which must be there; the stated total weight is the sum over ALL of them (as Config::unpack_validator_set
checks it), while only the first MAIN -- the ones that sign masterchain blocks -- become members, and
their weights are the set's TOTAL-WEIGHT (the signature threshold's base).  No member key may repeat."
  (let* ((s (cell-slice cell)) (tag (load-uint s 8)))
    (%prove (member tag '(#x11 #x12)) "not a validator set (constructor ~X)" tag)
    (multiple-value-bind (since s) (load-uint (skip-bits s 8) 32)
      (multiple-value-bind (until s) (load-uint s 32)
        (multiple-value-bind (total s) (load-uint s 16)
          (multiple-value-bind (main s) (load-uint s 16)
            (multiple-value-bind (stated s) (if (= tag #x12) (load-uint s 64) (values nil s))
              (let ((root (if (= tag #x12) (load-maybe-ref s) (load-ref s)))
                    (seen (make-hash-table :test #'equalp))
                    (weight 0) (all-weight 0)
                    (members '()))
                (%prove (<= 1 main total) "a validator set with ~D main validators of ~D" main total)
                (dotimes (i total)
                  (multiple-value-bind (value found) (dict-lookup root i 16)
                    (%prove found "validator ~D of ~D is missing from the list" i total)
                    (multiple-value-bind (key w adnl) (%parse-validator-descr value)
                      (%prove (plusp w) "validator ~D has weight 0" i)
                      (incf all-weight w)
                      (when (< i main)
                        (%prove (not (gethash key seen)) "validator key repeated in the set")
                        (setf (gethash key seen) t)
                        (incf weight w)
                        (push (list (adnl-short-id key) key w adnl) members)))))
                (%prove (< all-weight (ash 1 64)) "total validator weight overflows 64 bits")
                (when stated
                  (%prove (= stated all-weight) "stated total weight ~D, the validators add up to ~D" stated all-weight))
                (make-validator-set :since since :until until :main main :total-weight weight
                                    :members (coerce (nreverse members) 'vector))))))))))

(defun %signature-set-cc-seqno (signature-set)
  "The catchain seqno of a liteServer.signatureSet (ordinary: catchain_seqno, simplex: cc_seqno)."
  (if (tl-is signature-set "liteServer.signatureSet.simplex")
      (tl-get signature-set :cc-seqno)
      (tl-get signature-set :catchain-seqno)))

(defvar *signature-set-counts* (list :ordinary 0 :simplex 0)
  "How many signature sets of each kind SIGNATURE-MESSAGE was asked about (the real-network diagnostics report it).")

(defun signature-message (block-id signature-set)
  "The octets every validator of SIGNATURE-SET signed for BLOCK-ID, as block::BlockSignatureSet*::to_sign:
an ordinary set signs ton.blockId(root, file); a Simplex set (a final vote of the new consensus) signs
consensus.dataToSign(session_id, consensus.simplex.finalizeVote(consensus.candidateId(slot, hash of the
candidate))), where the candidate -- consensus.candidateHashData, serialized boxed -- must be one for
exactly BLOCK-ID."
  (cond
    ((tl-is signature-set "liteServer.signatureSet.ordinary")
     (incf (getf *signature-set-counts* :ordinary))
     (tl-encode (tl-make "ton.blockId" :root-cell-hash (tl-get block-id :root-hash)
                                       :file-hash (tl-get block-id :file-hash))))
    ((tl-is signature-set "liteServer.signatureSet.simplex")
     (incf (getf *signature-set-counts* :simplex))
     (let* ((candidate-octets (tl-get signature-set :candidate))
            (candidate (handler-case (tl-decode candidate-octets)
                         (error () (%prove nil "the Simplex candidate does not parse")))))
       (%prove (or (tl-is candidate "consensus.candidateHashDataOrdinary")
                   (tl-is candidate "consensus.candidateHashDataEmpty"))
               "the Simplex candidate is not a candidateHashData (~A)"
               (if (tl-obj-p candidate) (tl-obj-name candidate) "an unknown constructor"))
       (%prove (equalp (tl-encode candidate) candidate-octets) "the Simplex candidate is not in canonical form")
       (%prove (%same-block-id-p (tl-get candidate :block) block-id)
               "the Simplex candidate is for block ~D, not ~D" (tl-get (tl-get candidate :block) :seqno)
               (tl-get block-id :seqno))
       (%prove (= 32 (length (tl-get signature-set :session-id))) "a Simplex session id of the wrong length")
       (tl-encode (tl-make "consensus.dataToSign"
                           :session-id (tl-get signature-set :session-id)
                           :data (tl-encode (tl-make "consensus.simplex.finalizeVote"
                                                     :id (tl-make "consensus.candidateId"
                                                                  :slot (tl-get signature-set :slot)
                                                                  :hash (sha256 candidate-octets))))))))
    (t (%prove nil "unsupported signature set ~A" (tl-obj-name signature-set)))))

(defun plan-block-signatures (vset block-id signature-set)
  "The cheap half of checking SIGNATURE-SET over BLOCK-ID against the validator set VSET: every signature is
by a distinct member of VSET and has the right length, and the weight they claim is more than two thirds
of the total.  (VALUES CLAIMED-WEIGHT TOTAL-WEIGHT ENTRIES), ENTRIES a list of (PUBLIC-KEY MESSAGE SIGNATURE
SIGNER-ID) -- the signatures still to be verified, a pure computation (ED25519-FIRST-INVALID) that can be
batched with other links' and run on any thread."
  (let ((message (signature-message block-id signature-set))
        (by-id (make-hash-table :test #'equalp))
        (signed (make-hash-table :test #'equalp))
        (weight 0)
        (entries '()))
    (loop for m across (validator-set-members vset) do (setf (gethash (first m) by-id) m))
    (loop for sig across (tl-get signature-set :signatures)
          do (let* ((id (tl-get sig :node-id-short)) (member (gethash id by-id))
                    (octets (tl-get sig :signature)))
               (%prove member "a signature by ~A, who is not in the validator set" (octets->hex id))
               (%prove (not (gethash id signed)) "~A signed twice" (octets->hex id))
               (%prove (= 64 (length octets)) "a signature of ~D octets" (length octets))
               (push (list (second member) message octets id) entries)
               (setf (gethash id signed) t)
               (incf weight (third member))))
    (let ((total (validator-set-total-weight vset)))
      (%prove (> (* 3 weight) (* 2 total)) "signed weight ~D of ~D is not more than two thirds" weight total)
      (values weight total (nreverse entries)))))

(defun check-signature-entries (entries)
  "Verifies ENTRIES (as PLAN-BLOCK-SIGNATURES lists them) and signals a PROOF-ERROR naming the first
invalid signature's signer."
  (let ((bad (ed25519-first-invalid entries)))
    (when bad
      (%prove nil "invalid signature by ~A" (octets->hex (fourth (nth bad entries)))))))

(defun check-block-signatures (vset block-id signature-set)
  "(VALUES SIGNED-WEIGHT TOTAL-WEIGHT) of SIGNATURE-SET (a liteServer.signatureSet, ordinary or Simplex) over
BLOCK-ID, signers taken from VALIDATOR-SET VSET, provided every signature is by a distinct member
and valid and the signed weight is more than two thirds of the total."
  (multiple-value-bind (weight total entries) (plan-block-signatures vset block-id signature-set)
    (check-signature-entries entries)
    (values weight total)))

(defun check-signature-jobs (jobs)
  "JOBS: a list of (LABEL . ENTRIES), the signatures of several links.  Verifies them all, the links dealt
out in groups to the processors and each group checked as one batch; signals a PROOF-ERROR for the first
failing group's first invalid signature, labelled with its link."
  (let* ((jobs (remove nil jobs :key #'cdr))
         (workers (max 1 (min (worker-count) (length jobs))))
         (groups (let ((buckets (make-array workers :initial-element nil)))
                   ;; contiguous runs, so each group's batch shares the validators of neighbouring links
                   (loop for job in jobs
                         for i from 0
                         do (push job (svref buckets (min (1- workers) (floor (* i workers) (length jobs))))))
                   (map 'list #'reverse buckets)))
         (verdicts (parallel-map
                    (lambda (group)
                      (let* ((entries (loop for (nil . es) in group append es))
                             (bad (and entries (ed25519-first-invalid entries))))
                        (and bad
                             (let ((owner (loop for (label . es) in group
                                                do (if (< bad (length es))
                                                       (return (list label (fourth (nth bad es))))
                                                       (decf bad (length es))))))
                               owner))))
                    (remove nil groups))))
    (let ((failure (find-if #'identity verdicts)))
      (when failure
        (%prove nil "~A: invalid signature by ~A" (first failure) (octets->hex (second failure)))))))

;;; --- the configuration of a trusted block ----------------------------------------------

(define-proof-function masterchain-config-root (mc-state)
  "The root cell of the config dictionary (Hashmap 32 ^Cell) in the McStateExtra of MC-STATE."
  (let ((custom (getf (parse-shard-state-header mc-state) :custom)))
    (%prove custom "the masterchain state has no McStateExtra")
    (let ((s (cell-slice custom)))
      (%prove (= (load-uint s 16) #xcc26) "not a McStateExtra")
      (let ((s (nth-value 1 (load-maybe-ref (skip-bits s 16)))))   ; shard_hashes
        (load-ref (skip-bits s 256))))))                           ; config_addr, then the config dictionary

(define-proof-function config-param (config-root number)
  "The cell of configuration parameter NUMBER, or NIL when the proof shows it absent."
  (multiple-value-bind (value found) (dict-lookup config-root number 32)
    (and found (load-ref value))))

(defun validator-set-active-p (vset time)
  "Whether VSET is in force at unix TIME: since <= time < until."
  (and (<= (validator-set-since vset) time) (< time (validator-set-until vset))))

(define-proof-function key-block-config-root (block)
  "The root cell of the config dictionary (Hashmap 32 ^Cell) of BLOCK, a masterchain KEY block cell as a
liteserver reveals it in a forward link's config proof: Block -> BlockExtra -> McBlockExtra, whose
config:key_block?ConfigParams (config_addr:bits256 config:^(Hashmap 32 ^Cell)) follows key_block,
shard_hashes, shard_fees (a HashmapAugE: its extra is always present) and the ^[...] cell.
block::Config::extract_from_key_block reads the same path."
  (%prove (and (cell-p block) (not (cell-exotic-p block)) (= (load-uint (cell-slice block) 32) #x11ef55aa)
               (= 4 (length (cell-refs block))))
          "the config proof is not of a Block")
  (let* ((extra (svref (cell-refs block) 3))
         (es (cell-slice extra)))
    (%prove (= (load-uint es 32) #x4a33f6fd) "the config proof: not a BlockExtra")
    (%prove (= 1 (load-uint (skip-bits es 544) 1)) "the config proof: the masterchain block has no McBlockExtra")
    (%prove (= 4 (length (cell-refs extra))) "the config proof: a BlockExtra with a custom part has four references")
    (let* ((custom (svref (cell-refs extra) 3))
           (s (cell-slice custom)))
      (%prove (= (load-uint s 16) #xcca5) "the config proof: not a McBlockExtra")
      (%prove (= 1 (load-uint (skip-bits s 16) 1)) "the config proof: the block is not a key block (no configuration)")
      (let* ((s (nth-value 1 (load-maybe-ref (skip-bits s 17))))         ; shard_hashes
             (s (nth-value 1 (load-maybe-ref s)))                         ; shard_fees: root, then its extra
             (s (%skip-currency-collection s))
             (s (nth-value 1 (load-ref s))))                              ; ^[ prev_blk_signatures ... ]
        (load-ref (skip-bits s 256))))))                                  ; config_addr, then the dictionary

(define-proof-function validator-sets-at-root (root time)
  "The validator sets of the configuration dictionary ROOT (the current, 34, and the next, 36, when there is
one) whose window contains TIME: the ones that could have signed a block made then."
  (let ((candidates (remove nil (list (config-param root 34) (config-param root 36)))))
    (%prove candidates "the configuration has no validator set (parameter 34)")
    (remove-if-not (lambda (v) (validator-set-active-p v time)) (mapcar #'parse-validator-set candidates))))

(define-proof-function key-block-validator-sets (root)
  "The validator set a key block's configuration ROOT names, as Config::unpack reads it for
needValidatorSet: parameter 35 (the temporary set) when there is one, else 34.  That is all a node
reveals of the validator parameters in a forward link (the next set, 36, stays pruned), and all
tonlib uses: the key block's current set signs everything up to the next key block.  As a list of one."
  (let ((cell (or (handler-case (config-param root 35) (proof-error () nil))
                  (config-param root 34))))
    (%prove cell "the key block's configuration has no validator set (parameter 34)")
    (list (parse-validator-set cell))))

(define-proof-function validator-sets-at (mc-state time)
  "VALIDATOR-SETS-AT-ROOT of the configuration in the masterchain state MC-STATE."
  (validator-sets-at-root (masterchain-config-root mc-state) time))

;;; --- the validator-set hash and the masterchain order -----------------------------------
;;;
;;; A masterchain block's header carries gen_validator_list_hash_short and gen_catchain_seqno, and a
;;; signature set repeats them.  The hash is a CRC32C (block::compute_validator_set_hash) of the
;;; catchain seqno and the set in the order the node uses -- with shuffle_mc_validators (config
;;; parameter 28) a pseudo-random permutation seeded by the seqno (do_compute_validator_set).  All
;;; of it follows the node's source; the fakechain's hash is one tonlib itself recomputes.

(defvar *verify-validator-set-hash* t
  "Whether VERIFY-FORWARD-LINK recomputes the validator-set hash from the trusted configuration.  The
catchain seqno and the hash the signature set and the block header state must always agree.")

(defstruct (validator-prng (:conc-name vprng-) (:copier nil))
  "block::ValidatorSetPRNG for the masterchain: SHA-512 of seed(32) shard(u64) workchain(i32)
cc_seqno(u32), all big-endian, the seed (a 256-bit big-endian counter) incremented after each hash;
each hash is read as eight big-endian u64."
  (seed 0) (cc-seqno 0) (buffer nil) (pos 8))

(defun prng-next-ulong (g)
  (when (= (vprng-pos g) 8)
    (setf (vprng-buffer g)
          (ironclad:digest-sequence
           :sha512 (concatenate '(vector (unsigned-byte 8))
                                (uint->octets (vprng-seed g) 32)
                                (uint->octets #x8000000000000000 8)          ; the masterchain shard
                                (uint->octets (ldb (byte 32 0) -1) 4)        ; workchain -1
                                (uint->octets (ldb (byte 32 0) (vprng-cc-seqno g)) 4)))
          (vprng-seed g) (ldb (byte 256 0) (1+ (vprng-seed g)))
          (vprng-pos g) 0))
  (prog1 (octets->uint (subseq (vprng-buffer g) (* 8 (vprng-pos g)) (* 8 (1+ (vprng-pos g)))))
    (incf (vprng-pos g))))

(defun prng-next-ranged (g range)
  "An integer in 0 .. RANGE-1: the high half of RANGE times the next u64."
  (ash (* range (prng-next-ulong g)) -64))

(defun shuffle-masterchain-validators (items cc-seqno)
  "The sequence ITEMS in the order the node gives the masterchain validators of catchain seqno
CC-SEQNO when shuffle_mc_validators is set (a vector)."
  (let* ((n (length items))
         (idx (make-array n :initial-element 0))
         (g (make-validator-prng :cc-seqno cc-seqno)))
    (dotimes (i n)
      (let ((j (prng-next-ranged g (1+ i))))
        (setf (aref idx i) (aref idx j)
              (aref idx j) i)))
    (map 'vector (lambda (k) (elt items k)) idx)))

(defun compute-validator-set-hash (cc-seqno nodes)
  "block::compute_validator_set_hash: the CRC32C of the little-endian words magic -1877581587,
CC-SEQNO and the number of nodes, then for each node of NODES (lists of PUBLIC-KEY WEIGHT ADNL-ADDR)
its 32 key octets, its weight as 64 bits and its 32 adnl octets."
  (flet ((le (n bytes) (loop for i below bytes collect (ldb (byte 8 (* 8 i)) n))))
    (crc32c (coerce (append (le (ldb (byte 32 0) -1877581587) 4) (le cc-seqno 4) (le (length nodes) 4)
                            (loop for (key weight adnl) in nodes
                                  append (append (coerce key 'list) (le weight 8) (coerce adnl 'list))))
                    '(vector (unsigned-byte 8))))))

(defun masterchain-validator-set-hash (vset cc-seqno shuffle)
  "The hash a masterchain block of catchain seqno CC-SEQNO carries for VSET's main validators."
  (let ((members (validator-set-members vset)))
    (compute-validator-set-hash
     cc-seqno (map 'list (lambda (m) (list (second m) (third m) (fourth m)))
                   (if shuffle (shuffle-masterchain-validators members cc-seqno) members)))))

(defun check-validator-set-binding (vset signature-set info config-root)
  "That the signature set, the block header (INFO, from PARSE-BLOCK-INFO) and VSET agree on the
catchain seqno and the validator-set hash.  The hash is recomputed from VSET and the shuffle flag of
parameter 28 in CONFIG-ROOT when *VERIFY-VALIDATOR-SET-HASH*; a parameter 28 the proof leaves pruned
is not recomputed with."
  (let ((cc (getf info :catchain-seqno)) (hash (getf info :validator-list-hash)))
    (%prove (= (ldb (byte 32 0) (%signature-set-cc-seqno signature-set)) cc)
            "the signature set is for catchain seqno ~D, the block header says ~D"
            (%signature-set-cc-seqno signature-set) cc)
    (%prove (= (ldb (byte 32 0) (tl-get signature-set :validator-set-hash)) hash)
            "the signature set has validator set hash ~D, the block header ~D"
            (ldb (byte 32 0) (tl-get signature-set :validator-set-hash)) hash)
    (when *verify-validator-set-hash*
      (multiple-value-bind (cell known)
          (handler-case (values (config-param config-root 28) t) (proof-error () (values nil nil)))
        (when known
          (let ((expected (masterchain-validator-set-hash
                           vset cc (getf (parse-catchain-config cell) :shuffle-mc-validators))))
            (%prove (= expected hash)
                    "the validator set hashes to ~D at catchain seqno ~D, the block header says ~D"
                    expected cc hash)))))))

;;; --- links ----------------------------------------------------------------------------

(defun %same-block-id-p (a b)
  (and (= (tl-get a :workchain) (tl-get b :workchain))
       (= (tl-get a :shard) (tl-get b :shard))
       (= (tl-get a :seqno) (tl-get b :seqno))
       (equalp (tl-get a :root-hash) (tl-get b :root-hash))
       (equalp (tl-get a :file-hash) (tl-get b :file-hash))))

(defun %forward-link-parts (link trusted trusted-state-hash defer)
  "A liteServer.blockLinkForward LINK out of TRUSTED, a masterchain key block (or the zero state).  The
configuration the signers come from is read as BlockProofLink::validate reads it: from the zero state
(whose state hash is TRUSTED-STATE-HASH, its root hash) the config proof is a Merkle proof of that
state; from any other key block it is a Merkle proof of the BLOCK, bound to TRUSTED's own root hash, and
the configuration is the one in its McBlockExtra -- no state hash of TRUSTED is needed.
With DEFER, and a single validator set to check against (the key-block case), the signatures are not
verified here but returned, as the sixth value, for CHECK-SIGNATURE-JOBS.
(VALUES TO-ID TO-STATE-HASH KEY-BLOCK-P SIGNED-WEIGHT TOTAL-WEIGHT ENTRIES-TO-VERIFY)."
  (%prove (tl-is link "liteServer.blockLinkForward") "unsupported block link ~A" (tl-obj-name link))
  (let ((from (tl-get link :from)) (to (tl-get link :to)))
    (%prove (%same-block-id-p from trusted) "the link starts at block ~D, not at the trusted ~D"
            (tl-get from :seqno) (tl-get trusted :seqno))
    (%prove (and (= -1 (tl-get to :workchain)) (= (ldb (byte 64 0) (tl-get to :shard)) #x8000000000000000))
            "the link leads to a block that is not in the masterchain")
    (%prove (> (tl-get to :seqno) (tl-get trusted :seqno)) "the link does not move forward (~D to ~D)"
            (tl-get trusted :seqno) (tl-get to :seqno))
    (let* ((dest-roots (parse-boc (tl-get link :dest-proof)))
           (config-roots (parse-boc (tl-get link :config-proof))))
      (%prove (= 1 (length dest-roots)) "a link's header proof has ~D roots, not 1" (length dest-roots))
      (%prove (= 1 (length config-roots)) "a link's config proof has ~D roots, not 1" (length config-roots))
      (multiple-value-bind (block to-state-hash info) (verify-block-proof (first dest-roots) to :require-update nil)
        (declare (ignore block))
        (%prove (eq (and (tl-get link :to-key-block) t) (and (getf info :key-block) t))
                "the link says to_key_block ~A, the block says ~A" (tl-get link :to-key-block) (getf info :key-block))
        (let* ((config-root
                 (handler-case
                     (if (zerop (tl-get trusted :seqno))
                         (masterchain-config-root (verify-merkle-proof (first config-roots) trusted-state-hash))
                         (key-block-config-root (verify-merkle-proof (first config-roots) (tl-get trusted :root-hash))))
                   (boc-error (e) (%prove nil "config proof: ~A" e))))
               (sets (if (zerop (tl-get trusted :seqno))
                         (validator-sets-at-root config-root (getf info :gen-utime))
                         (key-block-validator-sets config-root)))
               (verdict nil)
               (pending nil))
          (%prove sets "no validator set of the trusted configuration covers time ~D" (getf info :gen-utime))
          (dolist (vset sets)
            (handler-case
                (multiple-value-bind (weight total entries) (plan-block-signatures vset to (tl-get link :signatures))
                  (if (and defer (null (cdr sets)))
                      (setf pending entries)
                      (check-signature-entries entries))
                  (check-validator-set-binding vset (tl-get link :signatures) info config-root)
                  (setf verdict (list weight total))
                  (return))
              (proof-error (e) (setf verdict e))))
          (when (typep verdict 'condition) (error verdict))
          (values to to-state-hash (getf info :key-block) (first verdict) (second verdict) pending))))))

(defun verify-forward-link (link trusted trusted-state-hash)
  "%FORWARD-LINK-PARTS with every signature verified before returning.
(VALUES TO-ID TO-STATE-HASH KEY-BLOCK-P SIGNED-WEIGHT TOTAL-WEIGHT)."
  (multiple-value-bind (to to-state-hash key weight total) (%forward-link-parts link trusted trusted-state-hash nil)
    (values to to-state-hash key weight total)))

(defun verify-back-link (link trusted)
  "A liteServer.blockLinkBack LINK out of TRUSTED to an OLDER masterchain block, as BlockProofLink::validate
checks a backward link: the header proof of the source block (bound to TRUSTED's id) gives its state hash;
the state proof must be a Merkle proof of that state whose prev_blocks lists the destination; the
destination's header proof (none for the zero state, whose root hash is its state hash) gives its key-block
flag; like a forward link's it reveals only the BlockInfo (check_block_header(vd_root, to) reads no state
hash), so its state_update is a pruned branch and TO-STATE-HASH is NIL.  (VALUES TO-ID TO-STATE-HASH KEY-BLOCK-P)."
  (with-proof-errors
    (%prove (tl-is link "liteServer.blockLinkBack") "unsupported block link ~A" (tl-obj-name link))
    (let ((from (tl-get link :from)) (to (tl-get link :to)))
      (%prove (%same-block-id-p from trusted) "the link starts at block ~D, not at the trusted ~D"
              (tl-get from :seqno) (tl-get trusted :seqno))
      (%prove (and (= -1 (tl-get to :workchain)) (= (ldb (byte 64 0) (tl-get to :shard)) #x8000000000000000))
              "the link leads to a block that is not in the masterchain")
      (%prove (< (tl-get to :seqno) (tl-get from :seqno)) "a backward link does not move back (~D to ~D)"
              (tl-get from :seqno) (tl-get to :seqno))
      (let ((state-hash (nth-value 1 (verify-block-proof (%single-root (tl-get link :proof) "back link source proof") from))))
        (let ((state (handler-case (verify-merkle-proof (%single-root (tl-get link :state-proof) "back link state proof")
                                                        state-hash)
                       (boc-error (e) (%prove nil "back link state proof: ~A" e)))))
          (%prove (%prev-blocks-contain-p state (tl-get to :seqno) (tl-get to :root-hash) (tl-get to :file-hash))
                  "the state of block ~D does not list block ~D as a previous masterchain block"
                  (tl-get from :seqno) (tl-get to :seqno)))
        (if (zerop (tl-get to :seqno))
            (progn (%prove (zerop (length (tl-get link :dest-proof))) "a zero state needs no destination proof")
                   (values to (tl-get to :root-hash) nil))
            (multiple-value-bind (block to-state-hash info)
                (verify-block-proof (%single-root (tl-get link :dest-proof) "back link destination proof") to
                                    :require-update nil)
              (declare (ignore block))
              (%prove (eq (and (tl-get link :to-key-block) t) (and (getf info :key-block) t))
                      "the link says to_key_block ~A, the block says ~A" (tl-get link :to-key-block) (getf info :key-block))
              (values to to-state-hash (getf info :key-block))))))))

(defun verify-partial-block-proof (proof trusted &key (trusted-state-hash
                                                       (and (zerop (tl-get trusted :seqno)) (tl-get trusted :root-hash))))
  "PROOF, a decoded liteServer.partialBlockProof, from the masterchain block TRUSTED (whose state
hash is TRUSTED-STATE-HASH; for the zero state, seqno 0, that is its root hash).  Walks the links,
each trusted only by the one before; returns (:TO ID :STATE-HASH HASH :COMPLETE BOOL :STEPS N
:KEY-BLOCK ID :KEY-STATE-HASH HASH), the block the chain reaches, whether the server says that is
the target, and the newest KEY block among the links' ends (NIL when no link ended at one): a client
starts its next sync from that, as a server answers only from key blocks.  Signals a PROOF-ERROR
if any link does not verify, or the chain does not end where the proof says it does."
  (with-proof-errors
    (%prove (%same-block-id-p (tl-get proof :from) trusted) "the proof is from block ~D, not the trusted ~D"
            (tl-get (tl-get proof :from) :seqno) (tl-get trusted :seqno))
    (let ((current trusted) (state-hash trusted-state-hash) (steps (tl-get proof :steps))
          (key-block nil) (key-state-hash nil))
      (let ((jobs '()))
        ;; the chain is walked in order, each link trusted by the one before; what is expensive -- the
        ;; validators' signatures -- is collected and checked afterwards, all together (CHECK-SIGNATURE-JOBS)
        (loop for link across steps
              for index from 1
              do (multiple-value-bind (to to-state-hash key weight total entries)
                     (if (tl-is link "liteServer.blockLinkBack")
                         (verify-back-link link current)
                         (%forward-link-parts link current state-hash t))
                   (declare (ignore weight total))
                   (when entries (push (cons (format nil "link ~D (to block ~D)" index (tl-get to :seqno)) entries) jobs))
                   (setf current to state-hash to-state-hash)
                   (when (and key (or (null key-block) (> (tl-get to :seqno) (tl-get key-block :seqno))))
                     (setf key-block to key-state-hash to-state-hash))))
        (check-signature-jobs (nreverse jobs)))
      (%prove (%same-block-id-p current (tl-get proof :to))
              "the chain of links ends at block ~D, the proof claims ~D"
              (tl-get current :seqno) (tl-get (tl-get proof :to) :seqno))
      (list :to current :state-hash state-hash :complete (and (tl-get proof :complete) t)
            :steps (length steps) :key-block key-block :key-state-hash key-state-hash))))

;;; --- one link at a time ---------------------------------------------------------------------

(defun proof-single-links (proof &key include-zero)
  "The forward links of PROOF (a decoded liteServer.partialBlockProof) each as a proof of its own, for
capturing real data: a list of plists (:KNOWN the link's start block :PROOF a one-link partialBlockProof
:KIND :SIMPLEX or :ORDINARY, by its signature set :FROM-SEQNO :TO-SEQNO).  A link from a key block verifies
alone (VERIFY-PARTIAL-BLOCK-PROOF of it from :KNOWN: its configuration proof is bound to the key block's
hash); a link from the zero state (seqno 0) needs the state hash too, so it is left out unless INCLUDE-ZERO.
Back links are skipped."
  (loop for link across (tl-get proof :steps)
        when (and (tl-is link "liteServer.blockLinkForward")
                  (or include-zero (plusp (tl-get (tl-get link :from) :seqno))))
          collect (list :known (tl-get link :from)
                        :proof (tl-make "liteServer.partialBlockProof" :complete t
                                                                       :from (tl-get link :from) :to (tl-get link :to)
                                                                       :steps (vector link))
                        :kind (if (tl-is (tl-get link :signatures) "liteServer.signatureSet.simplex") :simplex :ordinary)
                        :from-seqno (tl-get (tl-get link :from) :seqno)
                        :to-seqno (tl-get (tl-get link :to) :seqno))))

;;; --- the catchain configuration (parameter 28) -------------------------------------------

(define-proof-function parse-catchain-config (cell)
  "Configuration parameter 28 (CELL, or NIL when absent) as (:SHUFFLE-MC-VALIDATORS bool
:MC-CATCHAIN-LIFETIME :SHARD-CATCHAIN-LIFETIME :SHARD-VALIDATORS-LIFETIME :SHARD-VALIDATORS-NUM).
catchain_config#c1 has the four uint32 and no shuffle flag; catchain_config_new#c2 puts
flags:(## 7) (which must be 0) and shuffle_mc_validators:Bool in front of them.  Absent, the
node's defaults apply: no shuffle (the lifetimes are then NIL).  The #c2 layout follows the
record mc-config.cpp unpacks (shuffle_mc_validators); no recorded #c2 value has checked it yet."
  (if (null cell)
      (list :shuffle-mc-validators nil)
      (let* ((s (cell-slice cell)) (tag (load-uint s 8)))
        (%prove (member tag '(#xc1 #xc2)) "unknown catchain configuration constructor ~X" tag)
        (let ((s (skip-bits s 8)) (shuffle nil))
          (when (= tag #xc2)
            (multiple-value-bind (flags s1) (load-uint s 7)
              (%prove (zerop flags) "catchain configuration flags ~D (only 0 is defined)" flags)
              (multiple-value-bind (bit s2) (load-uint s1 1)
                (setf shuffle (= bit 1) s s2))))
          (multiple-value-bind (mc s) (load-uint s 32)
            (multiple-value-bind (shard s) (load-uint s 32)
              (multiple-value-bind (vlife s) (load-uint s 32)
                (list :shuffle-mc-validators shuffle :mc-catchain-lifetime mc :shard-catchain-lifetime shard
                      :shard-validators-lifetime vlife :shard-validators-num (load-uint s 32)))))))))

;;; --- configuration answers ------------------------------------------------------------

(defun %fully-visible-p (cell)
  "Whether CELL and everything below it is revealed: no pruned branch anywhere."
  (notany #'pruned-branch-p (collect-nodes cell)))

(defun verify-config-info (answer trusted-mc-block &key params all)
  "ANSWER, a decoded liteServer.configInfo (:ID :STATE-PROOF :CONFIG-PROOF), against the masterchain
block TRUSTED-MC-BLOCK (a blockIdExt tl-obj the caller trusts).  The answer must be about exactly
that block; its state proof (a block header proof) names the state hash; its config proof is a
Merkle proof of that state.  Returns (:CONFIG-ROOT cell :STATE-HASH hash :PARAMS alist), PARAMS
giving for each number asked for in PARAMS its cell, or NIL where the proof shows it absent;
asking for a parameter the proof does not reveal is an error, as is -- with ALL -- any pruned
cell anywhere in the configuration.  Signals a PROOF-ERROR otherwise."
  (with-proof-errors
    (let ((id (tl-get answer :id)))
      (%prove (%same-block-id-p id trusted-mc-block) "the configuration is of masterchain block ~D, not the trusted ~D"
              (tl-get id :seqno) (tl-get trusted-mc-block :seqno))
      (let ((header-roots (parse-boc (tl-get answer :state-proof)))
            (config-roots (parse-boc (tl-get answer :config-proof))))
        (%prove (= 1 (length header-roots)) "the state proof has ~D roots, not 1" (length header-roots))
        (%prove (= 1 (length config-roots)) "the config proof has ~D roots, not 1" (length config-roots))
        (multiple-value-bind (block state-hash) (verify-block-proof (first header-roots) id)
          (declare (ignore block))
          (let* ((state (handler-case (verify-merkle-proof (first config-roots) state-hash)
                          (boc-error (e) (%prove nil "config proof: ~A" e))))
                 (root (masterchain-config-root state)))
            (when all
              (dict-entries root 32 (lambda (v)
                                      (let ((param (load-ref v)))
                                        (%prove (%fully-visible-p param) "a configuration parameter is pruned")
                                        param))))
            (list :config-root root :state-hash state-hash
                  :params (mapcar (lambda (n)
                                    (let ((cell (config-param root n)))
                                      (when cell
                                        (%prove (%fully-visible-p cell) "configuration parameter ~D is pruned" n))
                                      (cons n cell)))
                                  params))))))))
