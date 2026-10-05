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

;;;; errors.lisp -- the ton-client condition hierarchy.  
  
(in-package :cl-ton)

(define-condition ton-error (simple-error) ()
  (:documentation "Base of every ton-client error."))

(defun ton-error (control &rest args)
  (error 'ton-error :format-control control :format-arguments args))

(define-condition tonlib-error (ton-error)
  ((code :initarg :code :reader tonlib-error-code)
   (message :initarg :message :reader tonlib-error-message))
  (:report (lambda (c s)
             (format s "tonlib error ~A: ~A"
                     (tonlib-error-code c) (tonlib-error-message c)))))

(define-condition emulator-error (ton-error) ())
