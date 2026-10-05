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

;;;; base64.lisp -- pure Base64 / Base64url codec over octet vectors.
;;;;
;;;; tonlibjson and the emulator exchange cells as standard Base64 BOCs;
;;;; user-friendly addresses use the URL-safe alphabet.

(in-package :cl-ton)


(defparameter *b64-standard*
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/")
(defparameter *b64-url*
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_")

(defun base64-encode (octets &key url (pad t))
  "Encode OCTETS.  URL selects the -_ alphabet; PAD NIL omits '='."
  (let* ((octets (as-octets octets))
         (alphabet (if url *b64-url* *b64-standard*))
         (n (length octets))
         (out (make-string-output-stream)))
    (loop for i from 0 below n by 3
          for chunk = (loop for j from i below (min n (+ i 3))
                            for acc = (aref octets j) then (logior (ash acc 8) (aref octets j))
                            finally (return acc))
          for have = (min 3 (- n i))
          for bits = (ash chunk (* 8 (- 3 have)))
          do (loop for k from 3 downto (- 3 have)
                   do (write-char (char alphabet (ldb (byte 6 (* 6 k)) bits)) out))
             (when pad
               (loop repeat (- 3 have) do (write-char #\= out))))
    (get-output-stream-string out)))

(defun base64-decode (string)
  "Decode STRING in either alphabet, with or without padding."
  (let ((vals (loop for c across string
                    for v = (cond ((char<= #\A c #\Z) (- (char-code c) 65))
                                  ((char<= #\a c #\z) (+ 26 (- (char-code c) 97)))
                                  ((char<= #\0 c #\9) (+ 52 (- (char-code c) 48)))
                                  ((or (char= c #\+) (char= c #\-)) 62)
                                  ((or (char= c #\/) (char= c #\_)) 63)
                                  ((or (char= c #\=) (char= c #\Newline) (char= c #\Return)) nil)
                                  (t (ton-error "Invalid base64 character ~S" c)))
                    when v collect v)))
    (let* ((nbits (* 6 (length vals)))
           (nbytes (floor nbits 8))
           (acc (reduce (lambda (a v) (logior (ash a 6) v)) vals :initial-value 0))
           (acc (ash acc (- (- nbits (* 8 nbytes))))))
      (if (zerop nbytes) (octets) (uint->octets acc nbytes)))))

(defun cell->base64 (cell &rest boc-options)
  (base64-encode (apply #'serialize-boc cell boc-options)))

(defun base64->cell (string)
  "Parse a single-root BOC given as Base64 and return the root cell."
  (let ((roots (parse-boc (base64-decode string))))
    (unless (= 1 (length roots))
      (ton-error "Expected a single-root BOC, got ~D roots" (length roots)))
    (first roots)))
