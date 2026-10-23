;;;; tl-generate.lisp -- the generator of cl-ton/src/tl-schema.lisp (a TEST-SIDE tool).
;;;;
;;;; The application carries the TL schemas (ton_api, lite_api, tonlib_api) as ordinary Lisp source,
;;;; cl-ton/src/tl-schema.lisp, and never reads a .tl file.  This file reads the vendored .tl files
;;;; (cl-ton/tests/tl/) and writes that source; TEST-TL-SCHEMA-GENERATED fails when the committed
;;;; file differs from what the vendored .tl files generate.  To update a schema: replace the .tl
;;;; file, evaluate (cl-ton::tl-write-schema-source), commit both, run the tests.

(in-package :cl-ton)

(eval-when (:compile-toplevel :load-toplevel :execute)

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
      (nreverse result))))

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

;;; --- the generator -------------------------------------------------------------------------------

(defun %tl-vendored-path (name)
  "The vendored schema NAME: in CL_TON_TL_DIR when set (the deployed test binary), else cl-ton/tests/tl/."
  (let ((dir (sb-posix:getenv "CL_TON_TL_DIR")))
    (if (and dir (plusp (length dir)))
        (merge-pathnames name (uiop:ensure-directory-pathname dir))
        (merge-pathnames (concatenate 'string "tests/tl/" name) (asdf:system-source-directory "cl-ton")))))

(defun tl-generate-declaration-texts ()
  "The non-builtin declarations of ton_api.tl then lite_api.tl, in file order (what TL-REGISTER takes)."
  (loop for file in '("ton_api.tl" "lite_api.tl")
        append (loop for (text . nil) in (tl-schema-chunks (%tl-vendored-path file))
                     unless (member (subseq text 0 (position-if (lambda (c) (member c '(#\Space #\#))) text))
                                    *tl-builtin-names* :test #'string=)
                       collect text)))

(defun tlapi-generate-declarations ()
  "Every non-builtin declaration of tonlib_api.tl, each (NAME KIND CLASS FIELDS)."
  (tlapi-read-declarations (%tl-vendored-path "tonlib_api.tl")))

(defun %tl-print-line (object)
  (let ((*package* (find-package :cl-ton)) (*print-pretty* nil) (*print-case* :upcase)
        (*print-readably* nil) (*print-circle* nil))
    (prin1-to-string object)))

(defun tl-schema-source ()
  "The text of cl-ton/src/tl-schema.lisp generated from the vendored .tl files."
  (with-output-to-string (o)
    (format o ";;;; tl-schema.lisp -- GENERATED by cl-ton/tests/tl-generate.lisp from cl-ton/tests/tl/*.tl; do not edit.~%")
    (format o ";;;;~%;;;; The TL schemas of the TON nodes (ton_api, lite_api) and of tonlib (tonlib_api) as Lisp data.  The~%")
    (format o ";;;; application never reads a .tl file; the test system checks this file against the vendored ones.~%~%")
    (format o "(in-package :cl-ton)~%~%")
    (format o "(defparameter *tl-schema-texts*~%  '(")
    (loop for (text . more) on (tl-generate-declaration-texts)
          do (format o "~A~:[)~;~%    ~]" (%tl-print-line text) more))
    (format o ")~%~%(dolist (declaration *tl-schema-texts*)~%  (tl-register declaration))~%~%")
    (format o "(defparameter *tlapi-schema-data*~%  '(")
    (loop for (d . more) on (tlapi-generate-declarations)
          do (format o "~A~:[)~;~%    ~]" (%tl-print-line d) more))
    (format o ")~%~%(tlapi-install *tlapi-schema-data*)~%")))

(defun tl-write-schema-source (&optional (path (merge-pathnames "src/tl-schema.lisp" (asdf:system-source-directory "cl-ton"))))
  (with-open-file (out path :direction :output :if-exists :supersede :external-format :utf-8)
    (write-string (tl-schema-source) out))
  path)

(defun test-tl-schema-generated (check-fn)
  "The registered schema equals what the vendored .tl files generate (CHECK-FN: the CHECK macro as a function)."
  (flet ((ck (name ok) (funcall check-fn name ok)))
    (format t "tl schema: the generated Lisp source is what the vendored .tl files generate~%")
    (ck "the ton_api / lite_api declarations of tl-schema.lisp equal the vendored files'"
        (equal (tl-generate-declaration-texts) *tl-schema-texts*))
    (ck "the tonlib_api declarations of tl-schema.lisp equal the vendored file's"
        (equal (tlapi-generate-declarations) *tlapi-schema-data*))
    (let ((committed (ignore-errors
                      (with-open-file (in (merge-pathnames "src/tl-schema.lisp" (asdf:system-source-directory "cl-ton"))
                                          :external-format :utf-8)
                        (let ((s (make-string (file-length in))))
                          (subseq s 0 (read-sequence s in)))))))
      (when committed
        (ck "...and the committed file is byte for byte the generator's output (cl-ton::tl-write-schema-source)"
            (string= committed (tl-schema-source)))))))
