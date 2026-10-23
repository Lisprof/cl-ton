;;;; json.lisp -- the one place where the application touches JSON.
;;;;
;;;; JSON reaches the application from two foreign sources only: the libemulator C API (its results are JSON text) and the
;;;; global-config files.  Both are read through these functions, which name the few jonathan functions the package imports.

(in-package :cl-ton)

(defun json-decode (string &key keep-literals)
  "STRING (JSON text) as a hash-table document.  KEEP-LITERALS reads true/false/null as :FALSE/:NULL (a config that is
written back unchanged), otherwise as jonathan's defaults."
  (if keep-literals
      (let ((*false-value* :false) (*null-value* :null))
        (parse string :as :hash-table))
      (parse string :as :hash-table)))

(defun json-encode (document)
  "DOCUMENT (a hash-table document, as JSON-DECODE returns) as JSON text."
  (to-json document))

(defun json-get (obj &rest keys)
  "Nested lookup in a hash-table document."
  (reduce (lambda (o k) (and (hash-table-p o) (gethash k o))) keys :initial-value obj))
