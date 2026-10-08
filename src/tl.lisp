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

(eval-when (:compile-toplevel :load-toplevel :execute)
  ;; These run when a file is COMPILED too (DEFINE-TL-SCHEMA / DEFINE-TLAPI-SCHEMA read the .tl
  ;; files while expanding), hence the EVAL-WHEN.

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

  (defun tl-schema-chunks (path)
    "The declarations of the .tl file at PATH, in file order: a list of (TEXT . KIND), TEXT
normalized (comments, markers and the semicolon removed), KIND :TYPE or :FUNCTION."
    (let* ((text (with-open-file (in path :external-format :utf-8)
                   (with-output-to-string (out)
                     (loop for line = (read-line in nil) while line
                           do (let ((c (search "//" line)))
                                (write-line (if c (subseq line 0 c) line) out))))))
           (kind :type) (result '()) (start 0))
      (loop for semi = (position #\; text :start start)
            while semi
            do (let ((chunk (subseq text start semi)))
                 (loop for (marker new) in '(("---functions---" :function) ("---types---" :type))
                       for pos = (search marker chunk)
                       when pos do (setf kind new
                                         chunk (concatenate 'string (subseq chunk 0 pos)
                                                            (subseq chunk (+ pos (length marker))))))
                 (let ((norm (tl-normalize-declaration chunk)))
                   (when (plusp (length norm)) (push (cons norm kind) result))))
               (setf start (1+ semi)))
      (nreverse result)))

  (defun tl-split-explicit-id (text)
    "A declaration's text -> (VALUES PLAIN-TEXT EXPLICIT-ID): `name#1a2b3c4d f:T = C` gives
`name f:T = C` and #x1A2B3C4D; EXPLICIT-ID is NIL when the name carries no #id (then the
constructor id is the CRC32 of the text)."
    (let* ((space (or (position #\Space text) (length text)))
           (hash (position #\# text :end space)))
      (if hash
          (values (concatenate 'string (subseq text 0 hash) (subseq text space))
                  (parse-integer text :start (1+ hash) :end space :radix 16))
          (values text nil))))

  (defparameter *tl-builtin-names*
    '("int" "long" "double" "string" "object" "function" "vector" "bytes" "true" "int128" "int256")
    "Constructors every .tl file declares for the language itself; the codec knows them as
types (TL-PARSE-TYPE), so they are not registered as constructors."))

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
              ;; the builtins `object` / `function`: a boxed value of any constructor
              ((string= text "object") (list :boxed "Object"))
              ((string= text "function") (list :boxed "Function"))
              ((and (> (length text) 2) (char= (char text 0) #\())
               (let* ((inner (subseq text 1 (1- (length text))))
                      (parts (tl-split-top-level inner)))
                 (cond ((string= (first parts) "vector")
                        (list :vector (tl-parse-type (second parts))))
                       ((null (rest parts)) (tl-parse-type (first parts))) ; redundant parentheses: (T)
                       (t (error "unsupported TL type application: ~A" text)))))
              (t (let* ((dot (position #\. text :from-end t))
                        (leaf (if dot (subseq text (1+ dot)) text)))
                   (if (upper-case-p (char leaf 0))
                       (list :boxed text)
                       (list :bare text))))))))

(defun tl-crc-text (decl)
  "The text tl-parser feeds to CRC32: as written, but with `(vector T)` spelled `vector T`
(no parentheses) and a redundant `(T)` spelled `T` (only
engine.validator.shardBlockVerifierConfig.shard uses it).  Both verified against the ids compiled
into libtonlibjson: 727 of the schema's 744 constructors occur there, the other 17 are ones
tonlib never parses (see *ABSENT-FROM-TONLIB-BINARY* in the tests)."
  (let ((out decl))
    (loop for pos = (search "(vector " out)
          while pos
          do (let ((end (position #\) out :start pos)))
               (setf out (concatenate 'string (subseq out 0 pos)
                                      (subseq out (1+ pos) end)
                                      (subseq out (1+ end))))))
    (loop for pos = (position #\( out)
          while pos
          do (let ((end (position #\) out :start pos)))
               (setf out (concatenate 'string (subseq out 0 pos)
                                      (subseq out (1+ pos) end)
                                      (subseq out (1+ end))))))
    out))

(defun tl-parse-declaration (text)
  "TEXT (`name#id fields = Class`, the #id optional) -> a TL-CON."
  (multiple-value-bind (decl explicit-id) (tl-split-explicit-id (tl-normalize-declaration text))
   (let* ((eq-pos (search " = " decl))
         (lhs (subseq decl 0 eq-pos))
         (result (subseq decl (+ eq-pos 3)))
         (parts (tl-split-top-level lhs))
         (name (first parts))
         (fields (loop for p in (rest parts)
                       for colon = (position #\: p)
                       collect (cons (subseq p 0 colon) (tl-parse-type (subseq p (1+ colon)))))))
    (make-tl-con :name name :id (or explicit-id (tl-crc32-id (tl-crc-text decl))) :fields fields
                 :result result :declaration decl))))

(defun tl-register (declaration)
  "Parse and register DECLARATION; refuses a name or constructor id that is already taken by a
different declaration (re-registering the same one is harmless)."
  (let* ((con (tl-parse-declaration declaration))
         (same-name (gethash (tl-con-name con) *tl-by-name*))
         (same-id (gethash (tl-con-id con) *tl-by-id*)))
    (when (or (and same-name (/= (tl-con-id same-name) (tl-con-id con)))
              (and same-id (string/= (tl-con-name same-id) (tl-con-name con))))
      (ton-error "TL declaration conflict: ~A (~8,'0X) against ~A (~8,'0X)"
                 (tl-con-name con) (tl-con-id con)
                 (tl-con-name (or same-name same-id)) (tl-con-id (or same-name same-id))))
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
    (:string (handler-case (sb-ext:octets-to-string (tl-get-bytes in) :external-format :utf-8)
               (tl-decode-error (e) (error e))
               (error () (tl-fail "TL: a string field is not valid UTF-8"))))
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

;;; --- the schema: lite_api.tl and ton_api.tl --------------------------------------
;;;
;;; The constructors are the vendored files' (cl-ton/tl/), read when this file is compiled, so
;;; the codec cannot disagree with them: names, field layouts, explicit `#id`s and CRC32 ids all
;;; come from the schema the TON nodes are built from.  Updating the schema means replacing
;;; the files and running the cl-ton test system, which checks the ids against the ones
;;; compiled into tonlibjson and round-trips every constructor.

(defmacro define-tl-schema (&rest relative-paths)
  "Register every non-builtin declaration of the .tl files RELATIVE-PATHS (relative to the file
being compiled), read now, at compile time, when the compiled file loads."
  (let ((base (or *compile-file-truename* *load-truename*)))
    `(dolist (declaration
              ',(loop for path in relative-paths
                      append (loop for (text . nil) in (tl-schema-chunks (merge-pathnames path base))
                                   unless (member (subseq text 0 (position-if (lambda (c) (member c '(#\Space #\#))) text))
                                                  *tl-builtin-names* :test #'string=)
                                     collect text)))
       (tl-register declaration))))

(define-tl-schema "../tl/ton_api.tl" "../tl/lite_api.tl")

;;; --- small conveniences used by the proxy / fakechain ----------------------

(defun tl-random-int256 ()
  (coerce (ironclad:random-data 32) 'tl-octets))

(defun tl-block-id-ext (&key (workchain -1) (shard (- (expt 2 63))) (seqno 0)
                          (root-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0))
                          (file-hash (make-array 32 :element-type '(unsigned-byte 8) :initial-element 0)))
  (tl-make "tonNode.blockIdExt" :workchain workchain :shard shard :seqno seqno
                                :root-hash root-hash :file-hash file-hash))

;;; --- tonlib_api.tl: the typed tonlib API ------------------------------------
;;;
;;; tonlib's API objects (cl-ton/tl/tonlib_api.tl) are not wire formats on this path: tonlib
;;; hands them around in memory and tonlibjson shows them as JSON.  So this section does not
;;; encode them to octets; it gives them a SCHEMA (read from the vendored file when this file
;;; is compiled, so the .tl text is not needed at run time), validated typed objects
;;; (TLAPI-MAKE / TLAPI-VALIDATE) and a bridge to and from tonlib's JSON conventions
;;; (TLAPI->PLIST / JSON->TLAPI) that the JSON backend and the test oracle use until the native
;;; engine replaces them.
;;;
;;; Types: int32 int53 int64 int256 bytes string secureBytes secureString Bool double, `#` flags
;;; with `flag.N?T` conditional fields, `vector<T>` / `(vector T)`, a bare constructor reference
;;; (lower-case leaf, exactly that constructor) or a class reference (upper-case leaf, any
;;; constructor of the class), plus the untyped Object and Function.
;;;
;;; JSON conventions (tonlib's tl_json): int32/int53 numbers, int64 a decimal string (a number is
;;; accepted when reading), int256/bytes/secureBytes base64 strings, Bool true/false, vectors
;;; arrays, objects hash tables or plists with "@type".

(eval-when (:compile-toplevel :load-toplevel :execute)

  (defun tlapi-parse-type (text)
    "Type text -> :int32 :int53 :int64 :int256 :bytes :string :secure-bytes :secure-string :bool
:double :flags :object :function, (:vector T), (:bare NAME), (:class NAME) or (:if FLAG BIT T)."
    (let ((q (position #\? text)))
      (cond
        (q (let* ((cond-part (subseq text 0 q)) (dot (position #\. cond-part)))
             (list :if (subseq cond-part 0 dot) (parse-integer cond-part :start (1+ dot))
                   (tlapi-parse-type (subseq text (1+ q))))))
        ((string= text "int32") :int32)
        ((string= text "int53") :int53)
        ((string= text "int64") :int64)
        ((string= text "int256") :int256)
        ((string= text "bytes") :bytes)
        ((string= text "string") :string)
        ((string= text "secureBytes") :secure-bytes)
        ((string= text "secureString") :secure-string)
        ((string= text "Bool") :bool)
        ((string= text "double") :double)
        ((string= text "#") :flags)
        ((string= text "Object") :object)
        ((string= text "Function") :function)
        ((and (> (length text) 8) (string= "(vector " text :end2 8))
         (list :vector (tlapi-parse-type (tl-normalize-declaration (subseq text 8 (1- (length text)))))))
        ((and (> (length text) 7) (string= "vector<" text :end2 7))
         (list :vector (tlapi-parse-type (subseq text 7 (1- (length text))))))
        (t (let* ((dot (position #\. text :from-end t))
                  (leaf (if dot (subseq text (1+ dot)) text)))
             (if (upper-case-p (char leaf 0)) (list :class text) (list :bare text)))))))

  (defparameter *tlapi-builtin-names*
    '("double" "string" "int32" "int53" "int64" "int256" "bytes" "secureString" "secureBytes"
      "object" "function" "boolFalse" "boolTrue" "vector"))

  (defun tlapi-parse-declaration (text kind)
    "One declaration (no trailing semicolon) -> (NAME KIND CLASS FIELDS), or NIL for a builtin."
    (let* ((decl (tl-normalize-declaration text))
           (eq-pos (search " = " decl :from-end t))
           (lhs (subseq decl 0 eq-pos))
           (class (subseq decl (+ eq-pos 3)))
           (parts (tl-split-top-level lhs))
           (name (first parts)))
      (unless (member name *tlapi-builtin-names* :test #'string=)
        (list name kind class
              (loop for p in (rest parts)
                    for colon = (position #\: p)
                    collect (cons (subseq p 0 colon) (tlapi-parse-type (subseq p (1+ colon)))))))))

  (defun tlapi-read-declarations (path)
    "Every non-builtin declaration of the tonlib .tl file at PATH, in file order, each
(NAME KIND CLASS FIELDS) with KIND :type or :function."
    (loop for (text . kind) in (tl-schema-chunks path)
          for d = (tlapi-parse-declaration text kind)
          when d collect d)))

(defstruct (tlapi-con (:copier nil))
  name kind class fields)

(defvar *tlapi-cons* (make-hash-table :test #'equal)
  "Constructor name -> TLAPI-CON, for every non-builtin declaration of tonlib_api.tl.")

(defun tlapi-install (declarations)
  (dolist (d declarations)
    (destructuring-bind (name kind class fields) d
      (setf (gethash name *tlapi-cons*)
            (make-tlapi-con :name name :kind kind :class class :fields fields)))))

(defmacro define-tlapi-schema (relative-path)
  "Read the .tl file at RELATIVE-PATH (relative to the file being compiled) now, at compile
time, and install its declarations when the compiled file loads."
  (let ((path (merge-pathnames relative-path (or *compile-file-truename* *load-truename*))))
    `(tlapi-install ',(tlapi-read-declarations path))))

(define-tlapi-schema "../tl/tonlib_api.tl")

(defun tlapi-find (name)
  (or (gethash name *tlapi-cons*) (ton-error "unknown tonlib API constructor ~A" name)))

(defun tlapi-constructor-names ()
  (let ((names '())) (maphash (lambda (k v) (declare (ignore v)) (push k names)) *tlapi-cons*) (sort names #'string<)))

(defun tlapi-function-p (name)
  (let ((con (gethash name *tlapi-cons*))) (and con (eq (tlapi-con-kind con) :function))))

;;; --- typed objects ------------------------------------------------------------

(defstruct (tlapi-obj (:constructor %make-tlapi-obj (name fields)) (:copier nil))
  (name nil :read-only t)       ; constructor name, e.g. "raw.getAccountState"
  (fields nil))                 ; plist keyed like :ACCOUNT-ADDRESS (TL-FIELD-KEY)

(defun tlapi-get (obj key) (getf (tlapi-obj-fields obj) key))

(defun tlapi-is (obj name) (and (tlapi-obj-p obj) (string= (tlapi-obj-name obj) name)))

(defun %tlapi-bad (path control &rest args)
  (ton-error "tonlib API ~A: ~?" path control args))

(defun %tlapi-octets-p (v) (typep v '(vector (unsigned-byte 8))))

(defun %tlapi-check (type value path)
  (flet ((need (ok what) (unless ok (%tlapi-bad path "expected ~A, got ~S" what value))))
    (ecase (if (consp type) (first type) type)
      (:int32 (need (typep value '(signed-byte 32)) "an int32"))
      (:int53 (need (typep value '(integer -9007199254740991 9007199254740991)) "an int53"))
      (:int64 (need (typep value '(signed-byte 64)) "an int64"))
      (:flags (need (typep value '(unsigned-byte 32)) "uint32 flags"))
      (:int256 (need (and (%tlapi-octets-p value) (= (length value) 32)) "32 octets"))
      ((:bytes :secure-bytes) (need (%tlapi-octets-p value) "an octet vector"))
      ((:string :secure-string) (need (stringp value) "a string"))
      (:bool (need (member value '(t nil)) "T or NIL"))
      (:double (need (realp value) "a real"))
      (:vector (need (or (listp value) (and (vectorp value) (not (stringp value)))) "a list or vector")
       (loop for e across (coerce value 'vector) for i from 0
             do (%tlapi-check (second type) e (format nil "~A[~D]" path i))))
      (:bare (need (tlapi-obj-p value) "an object")
       (unless (string= (tlapi-obj-name value) (second type))
         (%tlapi-bad path "expected a ~A, got a ~A" (second type) (tlapi-obj-name value)))
       (tlapi-validate value path))
      (:class (need (tlapi-obj-p value) "an object")
       (unless (string= (tlapi-con-class (tlapi-find (tlapi-obj-name value))) (second type))
         (%tlapi-bad path "expected a ~A, got a ~A" (second type) (tlapi-obj-name value)))
       (tlapi-validate value path))
      (:object (need (tlapi-obj-p value) "an object") (tlapi-validate value path))
      (:function (need (tlapi-obj-p value) "a function object")
       (unless (tlapi-function-p (tlapi-obj-name value))
         (%tlapi-bad path "~A is not a function" (tlapi-obj-name value)))
       (tlapi-validate value path)))))

(defun tlapi-validate (obj &optional (path nil))
  "OBJ if it is a well-formed typed object of the schema, else a TON-ERROR naming the offending
field.  Every field must be present (a conditional one exactly when its flag bit is set), no field
may be unknown, and every value must have its declared type (recursively)."
  (unless (tlapi-obj-p obj) (%tlapi-bad (or path "?") "not a typed object: ~S" obj))
  (let* ((con (tlapi-find (tlapi-obj-name obj)))
         (fields (tlapi-obj-fields obj))
         (path (if path (format nil "~A" path) (tlapi-obj-name obj)))
         (known '()))
    (dolist (f (tlapi-con-fields con))
      (let* ((fname (car f)) (type (cdr f)) (key (tl-field-key fname))
             (fpath (format nil "~A.~A" path fname))
             (conditional (and (consp type) (eq (first type) :if)))
             (expected (or (not conditional)
                           (logbitp (third type) (getf fields (tl-field-key (second type)) 0))))
             (present (tl-plist-has-key-p fields key)))
        (push key known)
        (cond ((and expected (not present)) (%tlapi-bad fpath "missing"))
              ((and present (not expected)) (%tlapi-bad fpath "present but its flag bit is clear"))
              (present (%tlapi-check (if conditional (fourth type) type) (getf fields key) fpath)))))
    (loop for (k nil) on fields by #'cddr
          unless (member k known) do (%tlapi-bad path "unknown field ~A" k))
    obj))

(defun tlapi-make (name &rest fields)
  "A validated typed object of constructor NAME; FIELDS is a plist keyed like :ACCOUNT-ADDRESS
(the TL field names, underscores as hyphens).  Nested objects are TLAPI-MAKE results."
  (tlapi-find name)
  (tlapi-validate (%make-tlapi-obj name (copy-list fields))))

;;; --- the JSON bridge ------------------------------------------------------------

(defun %tlapi->json (type value)
  (ecase (if (consp type) (first type) type)
    ((:int32 :int53 :flags) value)
    (:int64 (format nil "~D" value))
    ((:int256 :bytes :secure-bytes) (base64-encode value))
    ((:string :secure-string) value)
    (:bool (if value t :false))
    (:double value)
    (:vector (map 'list (lambda (e) (%tlapi->json (second type) e)) (coerce value 'vector)))
    ((:bare :class :object :function) (tlapi->plist value))))

(defun tlapi->plist (obj)
  "OBJ as the plist tonlibjson takes: (:|@type| NAME :|field_name| VALUE ...), fields in schema
order, nested objects as nested plists, int64 as a decimal string, bytes as base64, Bool as
T / :FALSE (what Jonathan turns into true / false)."
  (let ((con (tlapi-find (tlapi-obj-name obj))) (fields (tlapi-obj-fields obj)))
    (list* :|@type| (tlapi-obj-name obj)
           (loop for (fname . type) in (tlapi-con-fields con)
                 for key = (tl-field-key fname)
                 when (tl-plist-has-key-p fields key)
                   append (list (intern fname :keyword)
                                (%tlapi->json (if (eq (and (consp type) (first type)) :if) (fourth type) type)
                                              (getf fields key)))))))

(defun %json->tlapi (type json path)
  (flet ((need (ok what) (unless ok (%tlapi-bad path "expected ~A in JSON, got ~S" what json))))
    (ecase (if (consp type) (first type) type)
      ((:int32 :int53 :flags) (need (integerp json) "a number") json)
      (:int64 (cond ((integerp json) json)
                    ((stringp json) (or (ignore-errors (parse-integer json))
                                        (%tlapi-bad path "bad int64 string ~S" json)))
                    (t (need nil "an int64"))))
      ((:int256 :bytes :secure-bytes)
       (need (stringp json) "a base64 string")
       (let ((octets (coerce (base64-decode json) 'tl-octets)))
         (when (and (eq type :int256) (/= (length octets) 32))
           (%tlapi-bad path "int256 of ~D octets" (length octets)))
         octets))
      ((:string :secure-string) (need (stringp json) "a string") json)
      (:bool (and json (not (eq json :false)) t))
      (:double (need (realp json) "a number") (float json 1d0))
      (:vector (need (listp json) "an array")
       (loop for e in json for i from 0
             collect (%json->tlapi (second type) e (format nil "~A[~D]" path i))))
      ((:bare :class :object :function)
       (need (hash-table-p json) "an object")
       (let ((obj (%json->obj json path)))
         (case (if (consp type) (first type) type)
           (:bare (unless (string= (tlapi-obj-name obj) (second type))
                    (%tlapi-bad path "expected a ~A, got a ~A" (second type) (tlapi-obj-name obj))))
           (:class (unless (string= (tlapi-con-class (tlapi-find (tlapi-obj-name obj))) (second type))
                     (%tlapi-bad path "expected a ~A, got a ~A" (second type) (tlapi-obj-name obj)))))
         obj)))))

(defun %json->obj (json path)
  (let* ((name (gethash "@type" json))
         (con (progn (unless (stringp name) (%tlapi-bad path "JSON object without @type"))
                     (tlapi-find name)))
         (path (if (equal path "") name path)))
    (%make-tlapi-obj
     name
     (loop for (fname . type) in (tlapi-con-fields con)
           for json-value = (multiple-value-list (gethash fname json))
           when (second json-value)
             append (list (tl-field-key fname)
                          (%json->tlapi (if (eq (and (consp type) (first type)) :if) (fourth type) type)
                                        (first json-value) (format nil "~A.~A" path fname)))))))

(defun json->tlapi (json)
  "A decoded tonlibjson answer (a Jonathan hash table with \"@type\") -> a typed object.  Lenient
about what tonlib may add or omit (unknown JSON fields are dropped, absent ones stay absent -- use
TLAPI-VALIDATE to demand a complete object); strict about types and constructor classes."
  (%json->obj json ""))
