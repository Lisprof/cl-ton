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

;;;; tl.lisp -- Phase A: a generic TL (Type Language) codec over octet vectors,
;;;; plus the subset of lite_api.tl / ton_api.tl the ADNL-ext proxy and the
;;;; fakechain need.
;;;;
;;;; Schemas are written as the literal TL declaration text (the same text
;;;; that appears in the .tl files).  The constructor id is computed from
;;;; that text exactly the way TON's tl-parser does: CRC32-IEEE of the
;;;; normalized declaration, so there is no table of magic numbers to get
;;;; wrong -- and a handful of well-known ids are pinned in the unit tests
;;;; (tcp.ping, adnl.message.query, liteServer.query, ...) so a wrong CRC or
;;;; a mistyped declaration fails immediately.
;;;;
;;;; Wire rules implemented: int32/int64 little-endian, int256 as 32 raw
;;;; octets, bytes/string with the TL length prefix padded to 4, vector =
;;;; int32 count + elements, `#` as an unsigned int32, `Bool` as the boxed
;;;; boolTrue/boolFalse constructors, and `flags.N?T` conditional fields.
;;;; A field type that starts with a lower-case letter is BARE (no
;;;; constructor id on the wire); an upper-case one is BOXED (4-byte id first).
;;;;
;;;; A decoded object is a TL-OBJ.  A boxed value whose constructor is not in
;;;; the schema decodes to (ID . RAW-OCTETS) -- the id and the rest of the
;;;; buffer -- so nothing chokes on TL this file does not know about.

(in-package :cl-ton)

;;; --- output buffer ---------------------------------------------------------

(deftype tl-octets () '(simple-array (unsigned-byte 8) (*)))

(defun make-tl-out ()
  (make-array 64 :element-type '(unsigned-byte 8) :adjustable t :fill-pointer 0))

(defun tl-out-octets (out)
  (coerce out 'tl-octets))

(defun tl-put-u8 (out b) (vector-push-extend (logand b #xff) out))

(defun tl-put-uint-le (out value nbytes)
  (dotimes (i nbytes) (tl-put-u8 out (ldb (byte 8 (* 8 i)) value))))

(defun tl-put-int32 (out v) (tl-put-uint-le out v 4))
(defun tl-put-int64 (out v) (tl-put-uint-le out v 8))

(defun tl-put-raw (out octets)
  (loop for b across octets do (tl-put-u8 out b)))

(defun tl-put-int256 (out octets)
  (unless (= (length octets) 32)
    (ton-error "TL int256 must be 32 octets, got ~D" (length octets)))
  (tl-put-raw out octets))

(defun tl-put-bytes (out octets)
  (let ((n (length octets)))
    (if (< n 254)
        (tl-put-u8 out n)
        (progn (tl-put-u8 out 254) (tl-put-uint-le out n 3)))
    (tl-put-raw out octets)
    (let ((total (+ n (if (< n 254) 1 4))))
      (loop repeat (mod (- 4 (mod total 4)) 4) do (tl-put-u8 out 0)))))

(defun tl-string-octets (s)
  (if (stringp s) (sb-ext:string-to-octets s :external-format :utf-8) s))

;;; --- input cursor ----------------------------------------------------------

(deftype tl-octets-or-vector () '(vector (unsigned-byte 8)))

(defstruct (tl-in (:constructor make-tl-in (octets &optional (pos 0) (end (length octets)))))
  (octets nil :type tl-octets-or-vector)
  (pos 0 :type fixnum)
  (end 0 :type fixnum))

(define-condition tl-decode-error (ton-error) ())

(defun tl-fail (control &rest args)
  (error 'tl-decode-error :format-control control :format-arguments args))

(defun tl-need (in n)
  (when (> (+ (tl-in-pos in) n) (tl-in-end in))
    (tl-fail "TL: need ~D octets at offset ~D, only ~D left"
             n (tl-in-pos in) (- (tl-in-end in) (tl-in-pos in)))))

(defun tl-get-u8 (in)
  (tl-need in 1)
  (prog1 (aref (tl-in-octets in) (tl-in-pos in)) (incf (tl-in-pos in))))

(defun tl-get-uint-le (in nbytes)
  (tl-need in nbytes)
  (let ((v 0) (base (tl-in-pos in)))
    (dotimes (i nbytes) (setf v (logior v (ash (aref (tl-in-octets in) (+ base i)) (* 8 i)))))
    (incf (tl-in-pos in) nbytes)
    v))

(defun tl-get-uint32 (in) (tl-get-uint-le in 4))
(defun tl-get-int32 (in)
  (let ((v (tl-get-uint-le in 4))) (if (>= v #x80000000) (- v #x100000000) v)))
(defun tl-get-int64 (in)
  (let ((v (tl-get-uint-le in 8)))
    (if (>= v #x8000000000000000) (- v #x10000000000000000) v)))

(defun tl-get-raw (in n)
  (tl-need in n)
  (prog1 (subseq (tl-in-octets in) (tl-in-pos in) (+ (tl-in-pos in) n))
    (incf (tl-in-pos in) n)))

(defun tl-get-int256 (in) (coerce (tl-get-raw in 32) 'tl-octets))

(defun tl-get-bytes (in)
  (let* ((first (tl-get-u8 in))
         (n (if (< first 254) first (tl-get-uint-le in 3)))
         (data (tl-get-raw in n))
         (total (+ n (if (< first 254) 1 4))))
    (when (and (= first 254) (< n 254))
      (tl-fail "TL: non-canonical long bytes length ~D" n))
    (tl-get-raw in (mod (- 4 (mod total 4)) 4))
    (coerce data 'tl-octets)))

(defun tl-rest (in)
  (prog1 (coerce (subseq (tl-in-octets in) (tl-in-pos in) (tl-in-end in)) 'tl-octets)
    (setf (tl-in-pos in) (tl-in-end in))))

(defun tl-remaining (in) (- (tl-in-end in) (tl-in-pos in)))

;;; --- constructor ids -------------------------------------------------------

(defun tl-crc32-id (declaration)
  "CRC32-IEEE of DECLARATION (normalized TL text), as an unsigned 32-bit
integer -- the value that goes on the wire little-endian."
  (let ((d (ironclad:digest-sequence :crc32 (sb-ext:string-to-octets declaration))))
    (logior (ash (aref d 0) 24) (ash (aref d 1) 16) (ash (aref d 2) 8) (aref d 3))))

;;; --- schema registry -------------------------------------------------------

(defstruct (tl-con (:copier nil))
  name id fields result declaration)

(defvar *tl-by-name* (make-hash-table :test #'equal))
(defvar *tl-by-id* (make-hash-table))

(defun tl-normalize-declaration (text)
  "Collapse whitespace and drop the trailing semicolon."
  (let* ((s (string-trim '(#\Space #\Tab #\Newline #\Return #\;) text))
         (out (make-string-output-stream))
         (prev-space nil))
    (loop for c across s
          do (if (member c '(#\Space #\Tab #\Newline #\Return))
                 (unless prev-space (write-char #\Space out) (setf prev-space t))
                 (progn (write-char c out) (setf prev-space nil))))
    (get-output-stream-string out)))

(defun tl-split-top-level (s)
  "Split S on spaces that are not inside parentheses."
  (let ((parts '()) (depth 0) (start nil))
    (loop for i from 0 below (length s)
          for c = (char s i)
          do (cond ((char= c #\() (incf depth) (unless start (setf start i)))
                   ((char= c #\)) (decf depth))
                   ((and (char= c #\Space) (zerop depth))
                    (when start (push (subseq s start i) parts) (setf start nil)))
                   (t (unless start (setf start i)))))
    (when start (push (subseq s start) parts))
    (nreverse parts)))

(defun tl-parse-type (text)
  "Type expression -> internal form:
  :int :long :int128 :int256 :double :bytes :string :flags :true :bool
  (:vector T) (:bare NAME) (:boxed NAME) (:if FIELD BIT T)."
  (let ((q (position #\? text)))
    (if q
        (let* ((cond-part (subseq text 0 q))
               (dot (position #\. cond-part)))
          (list :if (subseq cond-part 0 dot) (parse-integer cond-part :start (1+ dot))
                (tl-parse-type (subseq text (1+ q)))))
        (cond ((string= text "int") :int)
              ((string= text "long") :long)
              ((string= text "int128") :int128)
              ((string= text "int256") :int256)
              ((string= text "double") :double)
              ((string= text "bytes") :bytes)
              ((string= text "string") :string)
              ((string= text "#") :flags)
              ((string= text "true") :true)
              ((string= text "Bool") :bool)
              ((and (> (length text) 2) (char= (char text 0) #\())
               (let* ((inner (subseq text 1 (1- (length text))))
                      (parts (tl-split-top-level inner)))
                 (unless (string= (first parts) "vector")
                   (error "unsupported TL type application: ~A" text))
                 (list :vector (tl-parse-type (second parts)))))
              (t (let* ((dot (position #\. text :from-end t))
                        (leaf (if dot (subseq text (1+ dot)) text)))
                   (if (upper-case-p (char leaf 0))
                       (list :boxed text)
                       (list :bare text))))))))

(defun tl-crc-text (decl)
  "The text tl-parser feeds to CRC32: as written, but with `(vector T)`
spelled `vector T` (no parentheses).  Verified against the ids compiled into
libtonlibjson (e.g. liteServer.getConfigParams)."
  (let ((out decl))
    (loop for pos = (search "(vector " out)
          while pos
          do (let ((end (position #\) out :start pos)))
               (setf out (concatenate 'string (subseq out 0 pos)
                                      (subseq out (1+ pos) end)
                                      (subseq out (1+ end))))))
    out))

(defun tl-parse-declaration (text)
  (let* ((decl (tl-normalize-declaration text))
         (eq-pos (search " = " decl))
         (lhs (subseq decl 0 eq-pos))
         (result (subseq decl (+ eq-pos 3)))
         (parts (tl-split-top-level lhs))
         (name (first parts))
         (fields (loop for p in (rest parts)
                       for colon = (position #\: p)
                       collect (cons (subseq p 0 colon) (tl-parse-type (subseq p (1+ colon)))))))
    (make-tl-con :name name :id (tl-crc32-id (tl-crc-text decl)) :fields fields
                 :result result :declaration decl)))

(defun tl-register (declaration)
  (let ((con (tl-parse-declaration declaration)))
    (setf (gethash (tl-con-name con) *tl-by-name*) con
          (gethash (tl-con-id con) *tl-by-id*) con)
    con))

(defun tl-find-con (name)
  (or (gethash name *tl-by-name*) (ton-error "unknown TL constructor ~A" name)))

(defun tl-id-of (name) (tl-con-id (tl-find-con name)))

;;; --- objects ---------------------------------------------------------------

(defstruct (tl-obj (:constructor %make-tl-obj (name fields)) (:copier nil))
  (name nil :read-only t)       ; constructor name, e.g. "liteServer.error"
  (fields nil))                 ; plist keyed by keywords: :QUERY-ID ...

(defun tl-field-key (field-name)
  (intern (string-upcase (substitute #\- #\_ field-name)) :keyword))

(defun tl-make (name &rest fields)
  "Build an object of constructor NAME; FIELDS is a plist keyed like
:QUERY-ID / :STATE-ROOT-HASH (TL field names, underscores as hyphens)."
  (tl-find-con name)
  (%make-tl-obj name (copy-list fields)))

(defun tl-get (obj key)
  (getf (tl-obj-fields obj) key))

(defun tl-is (obj name)
  (and (tl-obj-p obj) (string= (tl-obj-name obj) name)))

;;; --- encode ----------------------------------------------------------------

(defun tl-write-value (out type value fields con)
  (ecase (if (consp type) (first type) type)
    (:int (tl-put-int32 out value))
    (:flags (tl-put-int32 out value))
    (:long (tl-put-int64 out value))
    (:double (tl-put-int64 out value))
    (:int128 (tl-put-raw out value))
    (:int256 (tl-put-int256 out value))
    (:bytes (tl-put-bytes out value))
    (:string (tl-put-bytes out (tl-string-octets value)))
    (:true nil)
    (:bool (tl-encode-into out (tl-make (if value "boolTrue" "boolFalse")) t))
    (:vector (tl-put-int32 out (length value))
     (loop for e across (coerce value 'vector)
           do (tl-write-value out (second type) e fields con)))
    (:bare (tl-encode-into out value nil))
    (:boxed (tl-encode-into out value t))
    (:if (destructuring-bind (flag-field bit inner) (rest type)
           (let ((flags (getf fields (tl-field-key flag-field) 0)))
             (when (logbitp bit flags)
               (tl-write-value out inner value fields con)))))))

(defun tl-plist-has-key-p (plist key)
  (loop for (k nil) on plist by #'cddr thereis (eq k key)))

(defun tl-encode-into (out obj boxed)
  (when (consp obj)             ; an undecoded (id . raw) passes through verbatim
    (when boxed (tl-put-int32 out (car obj)))
    (tl-put-raw out (cdr obj))
    (return-from tl-encode-into out))
  (let* ((con (tl-find-con (tl-obj-name obj)))
         (fields (tl-obj-fields obj)))
    (when boxed (tl-put-int32 out (tl-con-id con)))
    (dolist (f (tl-con-fields con))
      (let* ((key (tl-field-key (car f)))
             (type (cdr f))
             (conditional (and (consp type) (eq (first type) :if)))
             (present (or (not conditional)
                          (logbitp (third type) (getf fields (tl-field-key (second type)) 0))))
             (base (if conditional (fourth type) type)))
        (when present
          (unless (or (tl-plist-has-key-p fields key) (eq base :true))
            (ton-error "TL encode ~A: missing field ~A" (tl-obj-name obj) (car f)))
          (tl-write-value out type (getf fields key) fields con))))
    out))

(defun tl-encode (obj)
  "OBJ as a boxed TL value (constructor id first) -> octet vector."
  (tl-out-octets (tl-encode-into (make-tl-out) obj t)))

(defun tl-encode-bare (obj)
  (tl-out-octets (tl-encode-into (make-tl-out) obj nil)))

;;; --- decode ----------------------------------------------------------------

(defun tl-read-value (in type fields-so-far)
  (ecase (if (consp type) (first type) type)
    (:int (tl-get-int32 in))
    (:flags (tl-get-uint32 in))
    (:long (tl-get-int64 in))
    (:double (tl-get-int64 in))
    (:int128 (coerce (tl-get-raw in 16) 'tl-octets))
    (:int256 (tl-get-int256 in))
    (:bytes (tl-get-bytes in))
    (:string (sb-ext:octets-to-string (tl-get-bytes in) :external-format :utf-8))
    (:true t)
    (:bool (let ((b (tl-decode-boxed in)))
             (cond ((tl-is b "boolTrue") t)
                   ((tl-is b "boolFalse") nil)
                   (t (tl-fail "TL: expected Bool, got ~A" b)))))
    (:vector (let ((n (tl-get-uint32 in)))
               (when (> n (tl-remaining in))
                 (tl-fail "TL: vector count ~D exceeds remaining ~D octets" n (tl-remaining in)))
               (coerce (loop repeat n collect (tl-read-value in (second type) fields-so-far))
                       'simple-vector)))
    (:bare (tl-decode-con in (tl-find-con (second type))))
    (:boxed (tl-decode-boxed in))
    (:if (destructuring-bind (flag-field bit inner) (rest type)
           (if (logbitp bit (getf fields-so-far (tl-field-key flag-field) 0))
               (tl-read-value in inner fields-so-far)
               nil)))))

(defun tl-decode-con (in con)
  (let ((fields '()))
    (dolist (f (tl-con-fields con))
      (let* ((type (cdr f))
             (conditional (and (consp type) (eq (first type) :if)))
             (present (or (not conditional)
                          (logbitp (third type)
                                   (getf fields (tl-field-key (second type)) 0)))))
        (when present
          (setf fields (append fields (list (tl-field-key (car f))
                                            (tl-read-value in type fields)))))))
    (%make-tl-obj (tl-con-name con) fields)))

(defun tl-decode-boxed (in)
  (let* ((id (tl-get-uint32 in))
         (con (gethash id *tl-by-id*)))
    (if con
        (tl-decode-con in con)
        (cons id (tl-rest in)))))

(defun tl-decode (octets)
  "Decode one boxed TL value occupying all of OCTETS.  Trailing octets after
a known constructor are an error; an unknown constructor decodes to
(ID . RAW-OCTETS)."
  (let* ((in (make-tl-in octets))
         (obj (tl-decode-boxed in)))
    (when (and (tl-obj-p obj) (plusp (tl-remaining in)))
      (tl-fail "TL: ~D trailing octets after ~A" (tl-remaining in) (tl-obj-name obj)))
    obj))

(defun tl-decode-prefix (octets)
  "Like TL-DECODE but tolerate trailing octets: (VALUES OBJ REST-OCTETS)."
  (let* ((in (make-tl-in octets))
         (obj (tl-decode-boxed in)))
    (values obj (tl-rest in))))

;;; --- the schema subset -----------------------------------------------------

(defparameter *tl-schema-declarations*
  '(;; --- ton_api.tl: transport ---
    "boolFalse = Bool"
    "boolTrue = Bool"
    "adnl.message.query query_id:int256 query:bytes = adnl.Message"
    "adnl.message.answer query_id:int256 answer:bytes = adnl.Message"
    "tcp.ping random_id:long = tcp.Pong"
    "tcp.pong random_id:long = tcp.Pong"
    "tcp.authentificate nonce:bytes = tcp.Message"
    "tcp.authentificationNonce nonce:bytes = tcp.Message"
    "tcp.authentificationComplete key:PublicKey signature:bytes = tcp.Message"
    "pk.ed25519 key:int256 = PrivateKey"
    "pub.ed25519 key:int256 = PublicKey"
    "adnl.id.short id:int256 = adnl.id.Short"
    ;; --- ton_api.tl: blocks ---
    "tonNode.blockId workchain:int shard:long seqno:int = tonNode.BlockId"
    "tonNode.blockIdExt workchain:int shard:long seqno:int root_hash:int256 file_hash:int256 = tonNode.BlockIdExt"
    "tonNode.zeroStateIdExt workchain:int root_hash:int256 file_hash:int256 = tonNode.ZeroStateIdExt"
    "ton.blockId root_cell_hash:int256 file_hash:int256 = ton.BlockId"
    ;; --- lite_api.tl: results ---
    "liteServer.error code:int message:string = liteServer.Error"
    "liteServer.accountId workchain:int id:int256 = liteServer.AccountId"
    "liteServer.masterchainInfo last:tonNode.blockIdExt state_root_hash:int256 init:tonNode.zeroStateIdExt = liteServer.MasterchainInfo"
    "liteServer.masterchainInfoExt mode:# version:int capabilities:long last:tonNode.blockIdExt last_utime:int now:int state_root_hash:int256 init:tonNode.zeroStateIdExt = liteServer.MasterchainInfoExt"
    "liteServer.currentTime now:int = liteServer.CurrentTime"
    "liteServer.version mode:# version:int capabilities:long now:int = liteServer.Version"
    "liteServer.blockData id:tonNode.blockIdExt data:bytes = liteServer.BlockData"
    "liteServer.blockHeader id:tonNode.blockIdExt mode:# header_proof:bytes = liteServer.BlockHeader"
    "liteServer.sendMsgStatus status:int = liteServer.SendMsgStatus"
    "liteServer.accountState id:tonNode.blockIdExt shardblk:tonNode.blockIdExt shard_proof:bytes proof:bytes state:bytes = liteServer.AccountState"
    "liteServer.runMethodResult mode:# id:tonNode.blockIdExt shardblk:tonNode.blockIdExt shard_proof:mode.0?bytes proof:mode.0?bytes state_proof:mode.1?bytes init_c7:mode.3?bytes lib_extras:mode.4?bytes exit_code:int result:mode.2?bytes = liteServer.RunMethodResult"
    "liteServer.shardInfo id:tonNode.blockIdExt shardblk:tonNode.blockIdExt shard_proof:bytes shard_descr:bytes = liteServer.ShardInfo"
    "liteServer.allShardsInfo id:tonNode.blockIdExt proof:bytes data:bytes = liteServer.AllShardsInfo"
    "liteServer.transactionInfo id:tonNode.blockIdExt proof:bytes transaction:bytes = liteServer.TransactionInfo"
    "liteServer.transactionList ids:(vector tonNode.blockIdExt) transactions:bytes = liteServer.TransactionList"
    "liteServer.transactionId mode:# account:mode.0?int256 lt:mode.1?long hash:mode.2?int256 = liteServer.TransactionId"
    "liteServer.transactionId3 account:int256 lt:long = liteServer.TransactionId3"
    "liteServer.signature node_id_short:int256 signature:bytes = liteServer.Signature"
    "liteServer.signatureSet validator_set_hash:int catchain_seqno:int signatures:(vector liteServer.signature) = liteServer.SignatureSet"
    "liteServer.blockLinkBack to_key_block:Bool from:tonNode.blockIdExt to:tonNode.blockIdExt dest_proof:bytes proof:bytes state_proof:bytes = liteServer.BlockLink"
    "liteServer.blockLinkForward to_key_block:Bool from:tonNode.blockIdExt to:tonNode.blockIdExt dest_proof:bytes config_proof:bytes signatures:liteServer.SignatureSet = liteServer.BlockLink"
    "liteServer.blockTransactions id:tonNode.blockIdExt req_count:# incomplete:Bool ids:(vector liteServer.transactionId) proof:bytes = liteServer.BlockTransactions"
    "liteServer.configInfo mode:# id:tonNode.blockIdExt state_proof:bytes config_proof:bytes = liteServer.ConfigInfo"
    ;; --- lite_api.tl: functions ---
    "liteServer.getMasterchainInfo = liteServer.MasterchainInfo"
    "liteServer.getMasterchainInfoExt mode:# = liteServer.MasterchainInfoExt"
    "liteServer.getTime = liteServer.CurrentTime"
    "liteServer.getVersion = liteServer.Version"
    "liteServer.getBlock id:tonNode.blockIdExt = liteServer.BlockData"
    "liteServer.getBlockHeader id:tonNode.blockIdExt mode:# = liteServer.BlockHeader"
    "liteServer.sendMessage body:bytes = liteServer.SendMsgStatus"
    "liteServer.getAccountState id:tonNode.blockIdExt account:liteServer.accountId = liteServer.AccountState"
    "liteServer.runSmcMethod mode:# id:tonNode.blockIdExt account:liteServer.accountId method_id:long params:bytes = liteServer.RunMethodResult"
    "liteServer.getShardInfo id:tonNode.blockIdExt workchain:int shard:long exact:Bool = liteServer.ShardInfo"
    "liteServer.getAllShardsInfo id:tonNode.blockIdExt = liteServer.AllShardsInfo"
    "liteServer.getOneTransaction id:tonNode.blockIdExt account:liteServer.accountId lt:long = liteServer.TransactionInfo"
    "liteServer.getTransactions count:# account:liteServer.accountId lt:long hash:int256 = liteServer.TransactionList"
    "liteServer.lookupBlock mode:# id:tonNode.blockId lt:mode.1?long utime:mode.2?int = liteServer.BlockHeader"
    "liteServer.listBlockTransactions id:tonNode.blockIdExt mode:# count:# after:mode.7?liteServer.transactionId3 reverse_order:mode.6?true want_proof:mode.5?true = liteServer.BlockTransactions"
    "liteServer.partialBlockProof complete:Bool from:tonNode.blockIdExt to:tonNode.blockIdExt steps:(vector liteServer.BlockLink) = liteServer.PartialBlockProof"
    "liteServer.getBlockProof mode:# known_block:tonNode.blockIdExt target_block:mode.0?tonNode.blockIdExt = liteServer.PartialBlockProof"
    "liteServer.getConfigAll mode:# id:tonNode.blockIdExt = liteServer.ConfigInfo"
    "liteServer.getConfigParams mode:# id:tonNode.blockIdExt param_list:(vector int) = liteServer.ConfigInfo"
    "liteServer.libraryEntry hash:int256 data:bytes = liteServer.LibraryEntry"
    "liteServer.libraryResult result:(vector liteServer.libraryEntry) = liteServer.LibraryResult"
    "liteServer.getLibraries library_list:(vector int256) = liteServer.LibraryResult"
    ;; --- lite_api.tl: envelope / prefixes ---
    "liteServer.query data:bytes = Object"
    "liteServer.queryPrefix = Object"
    "liteServer.waitMasterchainSeqno seqno:int timeout_ms:int = Object"))

(dolist (d *tl-schema-declarations*) (tl-register d))

;;; --- small conveniences used by the proxy / fakechain ----------------------

(defun tl-bytes32 (octets)
  "Left-pad/truncate nothing: assert a 32-octet int256 value."
  (unless (= (length octets) 32) (ton-error "expected 32 octets, got ~D" (length octets)))
  (coerce octets 'tl-octets))

(defun tl-random-int256 ()
  (coerce (ironclad:random-data 32) 'tl-octets))

(defun tl-block-id-ext (&key (workchain -1) (shard (- (expt 2 63))) (seqno 0)
                          (root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))
                          (file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
  (tl-make "tonNode.blockIdExt" :workchain workchain :shard shard :seqno seqno
                                :root-hash root-hash :file-hash file-hash))
