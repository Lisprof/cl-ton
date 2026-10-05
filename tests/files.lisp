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

;;;; files.lisp -- locate binaries BUILDER.LISP bundles into <bin>/env/.
;;;;
;;;; cl-ton/tests/ ships two platform binaries this project doesn't build
;;;; itself: TON's own `fift` interpreter and `proxy-liteserver`. Each is
;;;; named with an architecture suffix as downloaded (e.g.
;;;; "proxy-liteserver-linux-x86_64"); BUNDLED-ENV-BINARY takes the bare
;;;; logical name ("proxy-liteserver", "fift") and finds whichever matching
;;;; file is actually present, in this order:
;;;;
;;;;   1. <deploy runtime directory>/env/<name>*  (a built, deployed binary --
;;;;      see builder.lisp's TON-TRADER-ENV deploy hook)
;;;;   2. <cl-ton source directory>/tests/<name>* (REPL/test use straight out
;;;;      of a checkout, no build step)
;;;;   3. the TON_<NAME>_BINARY environment variable (existing override path;
;;;;      upper-cased, hyphens turned to underscores)
;;;;   4. <name> resolved against PATH
;;;;
;;;; Nil is returned (never an error) when none of the four resolve, so
;;;; callers keep deciding for themselves whether a missing binary is fatal
;;;; (see PROXY-LITESERVER-BINARY's use in bot.lisp: required once a bot is
;;;; actually opened, but only warned-about at deploy time) or merely means
;;;; skip an optional cross-check (fift, in cl-ton/tests/client.lisp).
;;;;
;;;; Results are cached per NAME so repeated calls (three OPEN-TONLIB sites
;;;; per bot, sixty-odd tests) don't re-stat the filesystem every time.

(in-package :cl-ton)

(defvar *bundled-env-binary-cache* (make-hash-table :test #'equal)
  "NAME -> resolved pathname or :none, memoizing BUNDLED-ENV-BINARY.")

(defun %first-matching-file (directory name)
  "First regular file under DIRECTORY whose name starts with NAME, or NIL.
DIRECTORY may not exist (a dev checkout with no build/ dir yet); that is
not an error here, just a non-match."
  (when (and directory (ignore-errors (uiop:directory-exists-p directory)))
    (find-if (lambda (p) (and (pathname-name p)
                              (uiop:string-prefix-p name (pathname-name p))))
             (sort (directory (merge-pathnames "*.*" directory)) #'string<
                   :key #'namestring))))

(defun %env-binary-var-name (name)
  "\"proxy-liteserver\" -> \"TON_PROXY-LITESERVER_BINARY\" -> normalized to
the existing TON_FIFT_BINARY / TON_PROXY_LITESERVER_BINARY convention
(hyphens as underscores, upper-cased)."
  (format nil "TON_~A_BINARY"
          (substitute #\_ #\- (string-upcase name))))

(defun %path-binary (name)
  "NAME resolved against PATH the way the shell would (first executable regular file\nnamed exactly NAME in a PATH directory), or NIL.  Walks PATH itself: `command -v` is a\nshell builtin, so running it through execvp never resolved anything."
  (let ((path (uiop:getenv "PATH")))
    (when (and path (plusp (length path)))
      (dolist (dir (uiop:split-string path :separator ":"))
        (when (plusp (length dir))
          (let ((p (ignore-errors (probe-file (merge-pathnames name (uiop:ensure-directory-pathname dir))))))
            (when (and p (pathname-name p)
                       (ignore-errors (logtest #o111 (sb-posix:stat-mode (sb-posix:stat (namestring p))))))
              (return (namestring p)))))))))

(defun bundled-env-binary (name)
  "Resolve the bundled binary called NAME (\"fift\", \"proxy-liteserver\") to
a path, or NIL if it isn't available anywhere. See the file header for the
four-step search order. Cached per NAME; call CLEAR-BUNDLED-ENV-BINARY-CACHE
if a test needs to force re-resolution."
  (let ((cached (gethash name *bundled-env-binary-cache*)))
    (if cached
        (and (not (eq cached :none)) cached)
        (let ((resolved
                (or (and (find-package :deploy)
                         (funcall (intern "DEPLOYED-P" :deploy))
                         (%first-matching-file
                          (merge-pathnames "env/"
                                           (funcall (intern "RUNTIME-DIRECTORY" :deploy)))
                          name))
                    ;; In a deployed build DEPLOY:CLEAR-ASDF has emptied ASDF's
                    ;; registry, so the source directory is NIL (or the lookup
                    ;; signals): that just means "no checkout here", not an error.
                    (let ((src (ignore-errors (asdf:system-source-directory :cl-ton))))
                      (and src (%first-matching-file (merge-pathnames "tests/" src) name)))
                    (let ((env (uiop:getenv (%env-binary-var-name name))))
                      (and env (probe-file env) env))
                    (%path-binary name))))
          (let ((path (and resolved (namestring resolved))))   ; always a string, cached or not
            (setf (gethash name *bundled-env-binary-cache*) (or path :none))
            path)))))

(defun clear-bundled-env-binary-cache ()
  (clrhash *bundled-env-binary-cache*))
