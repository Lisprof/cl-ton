;;;; tlapi.lisp -- tests for the typed tonlib API (tl.lisp, schema cl-ton/tests/tl/tonlib_api.tl).
;;;;
;;;; Four layers: the schema (counted independently of the parser), typed objects and their
;;;; validation (including every way to get one wrong), the JSON bridge (exactly the requests
;;;; tonlib.lisp builds by hand today), and a live A/B: typed requests go to the real
;;;; tonlibjson.so on the fakechain and its answers come back as typed, complete objects.
;;;; Last, the hand-written lite/ton declarations must still agree with the vendored files.

(in-package :cl-ton/test)

(defun %tl-file (name)
  "The vendored schema NAME: in CL_TON_TL_DIR when set (the deployed test binary, whose run-tests.sh
points it at the copy beside the binary), else in the checkout via ASDF."
  (let ((dir (sb-posix:getenv "CL_TON_TL_DIR")))
    (if (and dir (plusp (length dir)))
        (merge-pathnames name (uiop:ensure-directory-pathname dir))
        (asdf:system-relative-pathname :cl-ton (format nil "tests/tl/~A" name)))))

(defun %raw-declarations (name)
  "Alist (constructor-name . normalized declaration text) of the vendored file NAME, by a
deliberately crude reader (comments stripped, split on semicolons, markers dropped) that shares
no code with the schema parser."
  (let* ((text (with-open-file (in (%tl-file name) :external-format :utf-8)
                 (with-output-to-string (out)
                   (loop for line = (read-line in nil) while line
                         do (let ((c (search "//" line))) (write-line (if c (subseq line 0 c) line) out))))))
         (result '()) (start 0))
    (loop for semi = (position #\; text :start start) while semi
          do (let ((chunk (subseq text start semi)))
               (dolist (m '("---functions---" "---types---"))
                 (let ((p (search m chunk)))
                   (when p (setf chunk (concatenate 'string (subseq chunk 0 p) (subseq chunk (+ p (length m))))))))
               (let ((d (cl-ton::tl-normalize-declaration chunk)))
                 (when (plusp (length d))
                   (push (cons (subseq d 0 (position #\Space d)) d) result))))
             (setf start (1+ semi)))
    (nreverse result)))

(defun %tlapi-equal (a b)
  (cond ((and (cl-ton:tlapi-obj-p a) (cl-ton:tlapi-obj-p b))
         (and (string= (cl-ton:tlapi-obj-name a) (cl-ton:tlapi-obj-name b))
              (let ((fa (cl-ton::tlapi-obj-fields a)) (fb (cl-ton::tlapi-obj-fields b)))
                (and (= (length fa) (length fb))
                     (loop for (k v) on fa by #'cddr
                           always (and (cl-ton::tl-plist-has-key-p fb k) (%tlapi-equal v (getf fb k))))))))
        ((and (listp a) (listp b) (or a b)) (and (= (length a) (length b)) (every #'%tlapi-equal a b)))
        ((and (vectorp a) (vectorp b) (not (stringp a))) (equalp a b))
        (t (equal a b))))

(defun %plist-p (x) (and (consp x) (keywordp (first x))))

(defun %json-shape-equal (a b)
  "Equality of request plists where the ORDER of an object's keys does not matter (JSON objects
are unordered); lists of non-plists compare element by element."
  (cond ((and (%plist-p a) (%plist-p b))
         (and (= (length a) (length b))
              (loop for (k v) on a by #'cddr
                    always (and (member k b) (%json-shape-equal v (getf b k))))))
        ((and (listp a) (listp b)) (and (= (length a) (length b)) (every #'%json-shape-equal a b)))
        (t (equal a b))))

(defun %rejects (name &rest fields)
  "True when TLAPI-MAKE refuses the object."
  (%signals error (apply #'cl-ton:tlapi-make name fields)))

(defun %addr-obj (s) (cl-ton:tlapi-make "accountAddress" :account-address s))

(defun %zeros (n) (make-array n :element-type '(unsigned-byte 8) :initial-element 0))

(defun test-tlapi-schema ()
  (format t "tonlib API: schema read from the vendored tonlib_api.tl~%")
  (let* ((raw (%raw-declarations "tonlib_api.tl"))
         (builtins 14)
         (functions (let ((n 0) (fn nil))
                      (with-open-file (in (%tl-file "tonlib_api.tl"))
                        (loop for line = (read-line in nil) while line
                              do (cond ((search "---functions---" line) (setf fn t))
                                       ((search "---types---" line) (setf fn nil))
                                       ((and fn (plusp (length line)) (not (search "//" line :end2 (min 2 (length line))))
                                             (find #\= line) (find #\; line))
                                        (incf n)))))
                      n)))
    (check "every non-builtin declaration of the file is in the registry (counted independently)"
           (= (length (cl-ton:tlapi-constructor-names)) (- (length raw) builtins)))
    (check "the function declarations are exactly the registry's functions"
           (= functions (count-if #'cl-ton:tlapi-function-p (cl-ton:tlapi-constructor-names))))
    (check "pinned: 220 constructors, 85 functions in this schema revision"
           (and (= 220 (length (cl-ton:tlapi-constructor-names)))
                (= 85 (count-if #'cl-ton:tlapi-function-p (cl-ton:tlapi-constructor-names)))))
    (check "every declaration's fields and class match the raw text (names, order, class)"
           (every (lambda (entry)
                    (let ((con (gethash (car entry) cl-ton::*tlapi-cons*)))
                      (or (null con)       ; a builtin
                          (let* ((d (cdr entry))
                                 (eq-pos (search " = " d :from-end t)))
                            (and (string= (cl-ton::tlapi-con-class con) (subseq d (+ eq-pos 3)))
                                 (equal (mapcar #'car (cl-ton::tlapi-con-fields con))
                                        (loop for tok in (rest (cl-ton::tl-split-top-level (subseq d 0 eq-pos)))
                                              collect (subseq tok 0 (position #\: tok)))))))))
                  raw))
    (check "every constructor the application uses today exists, functions as functions"
           (every (lambda (n) (cl-ton:tlapi-function-p n))
                  '("init" "sync" "blocks.getMasterchainInfo" "blocks.getShards" "blocks.getTransactions"
                    "raw.getAccountState" "raw.getTransactions" "raw.sendMessageReturnHash" "smc.load"
                    "smc.runGetMethod" "smc.forget" "smc.getLibraries" "getConfigAll" "getShardAccountCell"
                    "withBlock")))
    (check "...and the data constructors"
           (every (lambda (n) (and (gethash n cl-ton::*tlapi-cons*) (not (cl-ton:tlapi-function-p n))))
                  '("options" "config" "keyStoreTypeInMemory" "keyStoreTypeDirectory" "accountAddress"
                    "ton.blockIdExt" "internal.transactionId" "blocks.accountTransactionId" "smc.methodIdName"
                    "tvm.cell" "tvm.slice" "tvm.numberDecimal" "tvm.stackEntrySlice" "tvm.stackEntryNumber"
                    "tvm.stackEntryCell")))
    (check "bare vs class types: ton.blockIdExt is a constructor, ton.BlockIdExt its class"
           (let ((f (cdr (assoc "id" (cl-ton::tlapi-con-fields (cl-ton::tlapi-find "blocks.getShards")) :test #'string=))))
             (equal f '(:bare "ton.blockIdExt"))))
    (check "(vector T) and vector<T> both parse; a conditional field parses with its flag and bit"
           (and (equal (cl-ton::tlapi-parse-type "(vector blocks.shardBlockLink)") '(:vector (:bare "blocks.shardBlockLink")))
                (equal (cl-ton::tlapi-parse-type "vector<tvm.StackEntry>") '(:vector (:class "tvm.StackEntry")))
                (equal (cl-ton::tlapi-parse-type "mode.1?int64") '(:if "mode" 1 :int64))))))

(defun test-tlapi-validation ()
  (format t "tonlib API: typed objects and validation~%")
  (let ((addr (%addr-obj "EQ00")))
    (check "a well-formed request builds"
           (cl-ton:tlapi-is (cl-ton:tlapi-make "raw.getAccountState" :account-address addr) "raw.getAccountState"))
    (check "tlapi-get reads a field" (equal "EQ00" (cl-ton:tlapi-get addr :account-address)))
    (check "a missing field is rejected" (%rejects "raw.getAccountState"))
    (check "an unknown field is rejected" (%rejects "raw.getAccountState" :account-address addr :nonsense 1))
    (check "an unknown constructor is rejected" (%rejects "raw.noSuchThing"))
    (check "a wrong scalar type is rejected (string field given a number)" (%rejects "accountAddress" :account-address 5))
    (check "int32 range (ton.blockIdExt seqno): 2^31 rejected, 2^31-1 and -2^31 accepted"
           (flet ((blk (seqno) (cl-ton:tlapi-make "ton.blockIdExt" :workchain -1 :shard 0 :seqno seqno
                                                                    :root-hash (%zeros 32) :file-hash (%zeros 32))))
             (and (%rejects "ton.blockIdExt" :workchain -1 :shard 0 :seqno (expt 2 31)
                                             :root-hash (%zeros 32) :file-hash (%zeros 32))
                  (blk (1- (expt 2 31))) (blk (- (expt 2 31))))))
    (check "flags (getConfigAll mode:#) are unsigned 32-bit: -1 and 2^32 rejected, 2^31 accepted"
           (and (%rejects "getConfigAll" :mode -1) (%rejects "getConfigAll" :mode (expt 2 32))
                (not (%rejects "getConfigAll" :mode (expt 2 31)))))
    (check "int64 range: 2^63 rejected, -2^63 accepted"
           (and (%rejects "internal.transactionId" :lt (expt 2 63) :hash (%zeros 32))
                (not (%rejects "internal.transactionId" :lt (- (expt 2 63)) :hash (%zeros 32)))))
    (check "int256 (smc.libraryEntry hash) must be exactly 32 octets; plain bytes (transactionId hash) any length"
           (and (%rejects "smc.libraryEntry" :hash (%zeros 31) :data (%zeros 4))
                (not (%rejects "smc.libraryEntry" :hash (%zeros 32) :data (%zeros 4)))
                (not (%rejects "internal.transactionId" :lt 1 :hash (%zeros 31)))))
    (check "bytes must be an octet vector, not a string" (%rejects "raw.sendMessageReturnHash" :body "AAAA"))
    (check "a class-typed field refuses another class (method id given an accountAddress)"
           (%rejects "smc.runGetMethod" :id 1 :method addr :stack '()))
    (check "...and takes any constructor of the class"
           (and (not (%rejects "smc.runGetMethod" :id 1 :method (cl-ton:tlapi-make "smc.methodIdName" :name "seqno") :stack '()))
                (not (%rejects "smc.runGetMethod" :id 1 :method (cl-ton:tlapi-make "smc.methodIdNumber" :number 85143) :stack '()))))
    (check "a bare-typed field refuses a different constructor"
           (%rejects "blocks.getShards" :id addr))
    (check "a Function field takes a function and refuses plain data"
           (let ((id (cl-ton:tlapi-make "ton.blockIdExt" :workchain -1 :shard (- (expt 2 63)) :seqno 1
                                                         :root-hash (%zeros 32) :file-hash (%zeros 32))))
             (and (not (%rejects "withBlock" :id id :function (cl-ton:tlapi-make "smc.load" :account-address addr)))
                  (%rejects "withBlock" :id id :function addr))))
    (check "vector elements are checked one by one, with the index in the error"
           (and (not (%rejects "smc.getLibraries" :library-list (list (%zeros 32) (%zeros 32))))
                (%rejects "smc.getLibraries" :library-list (list (%zeros 32) (%zeros 5)))
                (search "[1]" (handler-case (cl-ton:tlapi-make "smc.getLibraries" :library-list (list (%zeros 32) (%zeros 5)))
                                (error (e) (princ-to-string e)) (:no-error (x) (declare (ignore x)) "")))))
    (check "the error names the offending field path"
           (search "raw.getAccountState.account_address"
                   (handler-case (cl-ton:tlapi-make "raw.getAccountState") (error (e) (princ-to-string e)))))
    (check "conditional fields: present exactly when the flag bit is set"
           (and (not (%rejects "blocks.shortTxId" :mode 0))
                (not (%rejects "blocks.shortTxId" :mode 3 :account (%zeros 4) :lt 7))
                (%rejects "blocks.shortTxId" :mode 1)                       ; bit set, field missing
                (%rejects "blocks.shortTxId" :mode 0 :account (%zeros 4)))) ; field present, bit clear
    (check "validate also catches an object mutated after construction"
           (let ((o (cl-ton:tlapi-make "accountAddress" :account-address "EQ00")))
             (setf (getf (cl-ton::tlapi-obj-fields o) :account-address) 42)
             (%signals error (cl-ton:tlapi-validate o))))))

(defun %hand-requests ()
  "The requests tonlib.lisp builds by hand today (same shapes, same literals), as plists."
  (let* ((blk (list :|@type| "ton.blockIdExt" :|workchain| -1 :|shard| "-9223372036854775808" :|seqno| 5
                    :|root_hash| (cl-ton:base64-encode (%zeros 32)) :|file_hash| (cl-ton:base64-encode (%zeros 32))))
         (acc (list :|@type| "accountAddress" :|account_address| "EQ00")))
    (list
     (cons (list :|@type| "init"
                 :|options| (list :|@type| "options"
                                  :|config| (list :|@type| "config" :|config| "{}"
                                                  :|use_callbacks_for_network| :false
                                                  :|blockchain_name| "" :|ignore_cache| :false)
                                  :|keystore_type| (list :|@type| "keyStoreTypeInMemory")))
           (cl-ton:tlapi-make "init" :options (cl-ton:tlapi-make "options"
                                                :config (cl-ton:tlapi-make "config" :config "{}" :blockchain-name ""
                                                                                    :use-callbacks-for-network nil :ignore-cache nil)
                                                :keystore-type (cl-ton:tlapi-make "keyStoreTypeInMemory"))))
     (cons (list :|@type| "init"
                 :|options| (list :|@type| "options"
                                  :|config| (list :|@type| "config" :|config| "{}"
                                                  :|use_callbacks_for_network| :false
                                                  :|blockchain_name| "" :|ignore_cache| :false)
                                  :|keystore_type| (list :|@type| "keyStoreTypeDirectory" :|directory| ".tonlib/")))
           (cl-ton:tlapi-make "init" :options (cl-ton:tlapi-make "options"
                                                :config (cl-ton:tlapi-make "config" :config "{}" :blockchain-name ""
                                                                                    :use-callbacks-for-network nil :ignore-cache nil)
                                                :keystore-type (cl-ton:tlapi-make "keyStoreTypeDirectory" :directory ".tonlib/"))))
     (cons (list :|@type| "sync") (cl-ton:tlapi-make "sync"))
     (cons (list :|@type| "blocks.getMasterchainInfo") (cl-ton:tlapi-make "blocks.getMasterchainInfo"))
     (cons (list :|@type| "raw.getAccountState" :|account_address| acc)
           (cl-ton:tlapi-make "raw.getAccountState" :account-address (%addr-obj "EQ00")))
     (cons (list :|@type| "getConfigAll" :|mode| 0) (cl-ton:tlapi-make "getConfigAll" :mode 0))
     (cons (list :|@type| "getShardAccountCell" :|account_address| acc)
           (cl-ton:tlapi-make "getShardAccountCell" :account-address (%addr-obj "EQ00")))
     (cons (list :|@type| "raw.sendMessageReturnHash" :|body| (cl-ton:base64-encode (coerce '(1 2 3) '(vector (unsigned-byte 8)))))
           (cl-ton:tlapi-make "raw.sendMessageReturnHash" :body (coerce '(1 2 3) '(vector (unsigned-byte 8)))))
     ;; the schema requires private_key:InputKey (inputKeyFake: no key); the application's current
     ;; hand-built request leaves it out and tonlib's JSON parser lets it, the typed form sends it
     (cons (list :|@type| "raw.getTransactions" :|private_key| (list :|@type| "inputKeyFake")
                 :|account_address| acc
                 :|from_transaction_id| (list :|@type| "internal.transactionId" :|lt| "123456789012"
                                              :|hash| (cl-ton:base64-encode (%zeros 32))))
           (cl-ton:tlapi-make "raw.getTransactions" :private-key (cl-ton:tlapi-make "inputKeyFake")
                              :account-address (%addr-obj "EQ00")
                              :from-transaction-id (cl-ton:tlapi-make "internal.transactionId" :lt 123456789012 :hash (%zeros 32))))
     (cons (list :|@type| "blocks.getTransactions" :|id| blk :|mode| 135 :|count| 256
                 :|after| (list :|@type| "blocks.accountTransactionId"
                                :|account| (cl-ton:base64-encode (%zeros 32)) :|lt| "77"))
           (cl-ton:tlapi-make "blocks.getTransactions"
                              :id (cl-ton:tlapi-make "ton.blockIdExt" :workchain -1 :shard (- (expt 2 63)) :seqno 5
                                                                      :root-hash (%zeros 32) :file-hash (%zeros 32))
                              :mode 135 :count 256
                              :after (cl-ton:tlapi-make "blocks.accountTransactionId" :account (%zeros 32) :lt 77)))
     (cons (list :|@type| "smc.getLibraries" :|library_list| (list (cl-ton:base64-encode (%zeros 32))))
           (cl-ton:tlapi-make "smc.getLibraries" :library-list (list (%zeros 32))))
     (cons (list :|@type| "withBlock" :|id| blk
                 :|function| (list :|@type| "smc.load" :|account_address| acc))
           (cl-ton:tlapi-make "withBlock"
                              :id (cl-ton:tlapi-make "ton.blockIdExt" :workchain -1 :shard (- (expt 2 63)) :seqno 5
                                                                      :root-hash (%zeros 32) :file-hash (%zeros 32))
                              :function (cl-ton:tlapi-make "smc.load" :account-address (%addr-obj "EQ00"))))
     (cons (list :|@type| "smc.runGetMethod" :|id| 9           ; int53: a JSON number, unlike int64
                 :|method| (list :|@type| "smc.methodIdName" :|name| "seqno") :|stack| '())
           (cl-ton:tlapi-make "smc.runGetMethod" :id 9 :method (cl-ton:tlapi-make "smc.methodIdName" :name "seqno") :stack '())))))

(defun test-tlapi-json-bridge ()
  (format t "tonlib API: the JSON bridge~%")
  (let ((cases (%hand-requests)))
    (check "typed requests render to the plists the application builds by hand (all shapes, key order aside)"
           (every (lambda (c)
                    (or (%json-shape-equal (car c) (cl-ton:tlapi->plist (cdr c)))
                        (progn (format t "    differs: ~S~%        vs ~S~%" (car c) (cl-ton:tlapi->plist (cdr c))) nil)))
                  cases))
    (check "...and through real JSON text: encode, parse, decode gives the same typed object"
           (every (lambda (c)
                    (%tlapi-equal (cdr c)
                                  (cl-ton:json->tlapi (cl-ton::json-decode (cl-ton::json-encode (cl-ton:tlapi->plist (cdr c)))))))
                  cases))
    (check "Bool renders as JSON true/false"
           (let ((j (cl-ton::json-encode (cl-ton:tlapi->plist
                                          (cl-ton:tlapi-make "config" :config "x" :blockchain-name "" :use-callbacks-for-network t
                                                                      :ignore-cache nil)))))
             (and (search "\"use_callbacks_for_network\":true" j) (search "\"ignore_cache\":false" j)))))
  (check "int64 comes back from a JSON string or a JSON number alike"
         (every (lambda (text)
                  (= 77 (cl-ton:tlapi-get (cl-ton:json->tlapi (cl-ton::json-decode text)) :lt)))
                (list (format nil "{\"@type\":\"blocks.accountTransactionId\",\"account\":~S,\"lt\":\"77\"}"
                              (cl-ton:base64-encode (%zeros 32)))
                      (format nil "{\"@type\":\"blocks.accountTransactionId\",\"account\":~S,\"lt\":77}"
                              (cl-ton:base64-encode (%zeros 32))))))
  (check "decoding is strict about types: a wrong class, a bad int256 and a typeless object are refused"
         (flet ((bad (text) (%signals error (cl-ton:json->tlapi (cl-ton::json-decode text)))))
           (and (bad "{\"@type\":\"raw.getAccountState\",\"account_address\":{\"@type\":\"ok\"}}")
                (bad (format nil "{\"@type\":\"smc.libraryEntry\",\"hash\":~S,\"data\":\"\"}"
                             (cl-ton:base64-encode (%zeros 5))))
                (bad "{\"lt\":\"1\"}")
                (bad "{\"@type\":\"no.such.type\"}"))))
  (check "decoding is lenient where tonlib may differ: unknown fields dropped, absent ones stay absent"
         (let ((o (cl-ton:json->tlapi (cl-ton::json-decode "{\"@type\":\"error\",\"code\":500,\"message\":\"x\",\"@extra\":\"7\",\"future\":1}"))))
           (and (cl-ton:tlapi-is o "error") (= 500 (cl-ton:tlapi-get o :code))
                (equal "x" (cl-ton:tlapi-get o :message))
                (null (getf (cl-ton::tlapi-obj-fields o) :future)))))
  (check "tlapi-validate on a lenient decode demands completeness"
         (let ((o (cl-ton:json->tlapi (cl-ton::json-decode "{\"@type\":\"error\",\"code\":500}"))))
           (%signals error (cl-ton:tlapi-validate o)))))

(defun %typed-call (tl obj)
  "Send the typed request OBJ to the real tonlib and decode its answer into a typed object."
  (cl-ton:json->tlapi (cl-ton::tonlib-call tl obj)))

(defun test-tlapi-vs-tonlib ()
  (format t "tonlib API: typed requests against the real tonlibjson.so (fakechain)~%")
  (if (not (%libs-available-p))
      (skip-missing "typed tonlib API vs the real library (tonlib/libemulator shared libraries)")
      (call-with-fc-session
       (lambda (fc tl proxy cfg)
         (declare (ignore proxy cfg))
         (let* ((w (%seed-wallet fc))
                (addr (%addr-obj (cl-ton:address->string (wallet-address w)))))
           (cl-ton::fakechain-advance fc 1)
           (check "blocks.getMasterchainInfo: a complete typed blocks.masterchainInfo at the fakechain head"
                  (%until (lambda ()
                            (let ((r (%typed-call tl (cl-ton:tlapi-make "blocks.getMasterchainInfo"))))
                              (and (cl-ton:tlapi-is r "blocks.masterchainInfo")
                                   (cl-ton:tlapi-validate r)
                                   (cl-ton:tlapi-is (cl-ton:tlapi-get r :last) "ton.blockIdExt")
                                   (eql (cl-ton:tlapi-get (cl-ton:tlapi-get r :last) :seqno) (cl-ton::fc-head-seqno fc)))))
                          :seconds 15 :each (lambda () nil)))
           (let ((r (%typed-call tl (cl-ton:tlapi-make "raw.getAccountState" :account-address addr))))
             (check "raw.getAccountState: a complete typed raw.fullAccountState"
                    (and (cl-ton:tlapi-is r "raw.fullAccountState") (cl-ton:tlapi-validate r)))
             (check "...balance (int64) equals the fakechain's own"
                    (= (cl-ton:tlapi-get r :balance) (cl-ton::fakechain-account-balance fc (wallet-address w))))
             (check "...code and data are octet vectors, last_transaction_id a typed internal.transactionId"
                    (and (plusp (length (cl-ton:tlapi-get r :code)))
                         (typep (cl-ton:tlapi-get r :data) '(vector (unsigned-byte 8)))
                         (cl-ton:tlapi-is (cl-ton:tlapi-get r :last-transaction-id) "internal.transactionId"))))
           (let ((r (%typed-call tl (cl-ton:tlapi-make "getConfigAll" :mode 0))))
             (check "getConfigAll: a typed configInfo carrying a tvm.cell"
                    (and (cl-ton:tlapi-is r "configInfo") (cl-ton:tlapi-validate r)
                         (cl-ton:tlapi-is (cl-ton:tlapi-get r :config) "tvm.cell")
                         (plusp (length (cl-ton:tlapi-get (cl-ton:tlapi-get r :config) :bytes))))))
           (let* ((loaded (%typed-call tl (cl-ton:tlapi-make "smc.load" :account-address addr)))
                  (id (cl-ton:tlapi-get loaded :id)))
             (check "smc.load: a typed smc.info with an int64 id" (and (cl-ton:tlapi-is loaded "smc.info") (integerp id)))
             (let ((run (%typed-call tl (cl-ton:tlapi-make "smc.runGetMethod" :id id
                                                           :method (cl-ton:tlapi-make "smc.methodIdName" :name "seqno")
                                                           :stack '()))))
               (check "smc.runGetMethod: a typed smc.runResult, exit code 0, one typed stack number = 0"
                      (and (cl-ton:tlapi-is run "smc.runResult") (cl-ton:tlapi-validate run)
                           (eql 0 (cl-ton:tlapi-get run :exit-code))
                           (= 1 (length (cl-ton:tlapi-get run :stack)))
                           (let ((e (first (cl-ton:tlapi-get run :stack))))
                             (and (cl-ton:tlapi-is e "tvm.stackEntryNumber")
                                  (equal "0" (cl-ton:tlapi-get (cl-ton:tlapi-get e :number) :number)))))))
             (check "smc.forget: a typed ok"
                    (cl-ton:tlapi-is (%typed-call tl (cl-ton:tlapi-make "smc.forget" :id id)) "ok")))
           (let ((dest (fake-address #x66)))
             (cl-ton::tonlib-send-message tl (%transfer w 0 dest (nano 1/2)))
             (check "a transfer is emulated and the typed account state shows a transaction (lt > 0)"
                    (%until (lambda ()
                              (let ((r (%typed-call tl (cl-ton:tlapi-make "raw.getAccountState" :account-address addr))))
                                (plusp (cl-ton:tlapi-get (cl-ton:tlapi-get r :last-transaction-id) :lt))))
                            :seconds 30 :each (lambda () (cl-ton::fakechain-advance fc 1))))
             (let* ((st (%typed-call tl (cl-ton:tlapi-make "raw.getAccountState" :account-address addr)))
                    (last (cl-ton:tlapi-get st :last-transaction-id))
                    (txs (%typed-call tl (cl-ton:tlapi-make "raw.getTransactions"
                                                            :private-key (cl-ton:tlapi-make "inputKeyFake")
                                                            :account-address addr
                                                            :from-transaction-id last))))
               (check "raw.getTransactions with private_key inputKeyFake: the real library accepts the typed request"
                      (cl-ton:tlapi-is txs "raw.transactions"))
               (check "...the answer decodes to typed raw.transaction objects, the first being the last transaction"
                      (and (every (lambda (tx) (cl-ton:tlapi-is tx "raw.transaction")) (cl-ton:tlapi-get txs :transactions))
                           (plusp (length (cl-ton:tlapi-get txs :transactions)))
                           (= (cl-ton:tlapi-get (cl-ton:tlapi-get (first (cl-ton:tlapi-get txs :transactions)) :transaction-id) :lt)
                              (cl-ton:tlapi-get last :lt)))))
             (check "...and every decoded transaction validates as complete"
                    (let ((txs (%typed-call tl (cl-ton:tlapi-make
                                                "raw.getTransactions" :private-key (cl-ton:tlapi-make "inputKeyFake")
                                                :account-address addr
                                                :from-transaction-id
                                                (cl-ton:tlapi-get (%typed-call tl (cl-ton:tlapi-make "raw.getAccountState" :account-address addr))
                                                                  :last-transaction-id)))))
                      (every #'cl-ton:tlapi-validate (cl-ton:tlapi-get txs :transactions)))))
           (check "an error answer surfaces as the library's own error, naming the failing request"
                  (%signals error (%typed-call tl (cl-ton:tlapi-make "smc.forget" :id 99999999)))))))))

;;; --- the binary schema (lite_api.tl + ton_api.tl) is the vendored files' ------------------------

(defparameter *vendored-schema-sha256*
  '(("lite_api.tl" . "03247b1fe3cf861ac5d522cbc13a3afa4fb446357ff56ea32ca8ea707662f3e2")
    ("ton_api.tl" . "d6137cbeaa3324b632ccff597bc12c6bd7c194a7b6574fc57776266906cb90d6")
    ("tonlib_api.tl" . "d2a56b4e02bcf4a773a9e11d76afdf2ffa20eaafbbff2124f8750ebb8aa375b7"))
  "Pins: replacing a vendored schema is a conscious act.  When this fails after an update, re-run
the cl-ton test system (ids against tonlibjson, round trips, the live A/B) and re-pin.")

(defparameter *explicit-id-constructors*
  '(("liteServer.transactionId" #xB12F65AF) ("liteServer.signatureSet.ordinary" #xF644A6E6)
    ("liteServer.getValidatorStats" #x091A58BC) ("tonNode.capabilities" #xF5BF60C0)
    ("db.block.info" #x4AC6E727) ("collatorNode.pong" #x5BBF0521)
    ("consensus.broadcastExtraLegacy" #x921297FA))
  "Declarations the schema gives an explicit #id: that id is the wire id, not the CRC32 of the text.")

(defun %vendored-names (file)
  "Alist (name . plain-text) of the non-builtin declarations of FILE, by the crude reader,
the `#id` of an explicit-id declaration removed from the name."
  (loop for (full . text) in (%raw-declarations file)
        for hash = (position #\# full)
        for name = (subseq full 0 hash)
        unless (member name cl-ton::*tl-builtin-names* :test #'string=)
          collect (cons name (if hash (concatenate 'string name (subseq text (length full))) text))))

(defvar *fuzz-state* (sb-ext:seed-random-state 20261008))
(defun %rnd (n) (random n *fuzz-state*))

(defun %rnd-octets (n)
  (let ((v (make-array n :element-type '(unsigned-byte 8))))
    (dotimes (i n v) (setf (aref v i) (%rnd 256)))))

(defun %class-members ()
  "Class name -> its registered constructors."
  (let ((table (make-hash-table :test #'equal)))
    (maphash (lambda (name con) (declare (ignore name)) (push con (gethash (cl-ton::tl-con-result con) table)))
             cl-ton::*tl-by-name*)
    table))

(define-condition %fuzz-gave-up (error) ())

(defun %fuzz-value (type plist depth classes)
  (ecase (if (consp type) (first type) type)
    (:int (- (%rnd (expt 2 32)) (expt 2 31)))
    (:flags (%rnd (expt 2 31)))
    ((:long :double) (- (%rnd (expt 2 64)) (expt 2 63)))
    (:int128 (%rnd-octets 16))
    (:int256 (%rnd-octets 32))
    (:bytes (%rnd-octets (nth (%rnd 11) '(0 1 2 3 4 5 100 253 254 255 700))))
    (:string (let ((s (make-string (%rnd 12) :initial-element #\a)))
               (when (and (plusp (length s)) (zerop (%rnd 3))) (setf (char s 0) (code-char 233)))
               s))
    (:true t)
    (:bool (zerop (%rnd 2)))
    (:vector (if (> depth 2)
                 '()
                 (loop repeat (%rnd 3) collect (%fuzz-value (second type) plist (1+ depth) classes))))
    (:bare (%fuzz-object (cl-ton::tl-find-con (second type)) (1+ depth) classes))
    (:boxed (let ((members (if (member (second type) '("Object" "Function") :test #'string=)
                               (loop for con being the hash-values of cl-ton::*tl-by-name* collect con)
                               (gethash (second type) classes))))
              (unless members (error '%fuzz-gave-up))
              (when (> depth 7) (error '%fuzz-gave-up))
              (%fuzz-object (nth (%rnd (length members)) members) (1+ depth) classes)))
    (:if (%fuzz-value (fourth type) plist depth classes))))

(defun %fuzz-object (con depth classes)
  (let ((plist '()))
    (dolist (f (cl-ton::tl-con-fields con))
      (let* ((type (cdr f)) (key (cl-ton::tl-field-key (car f))))
        (when (or (not (and (consp type) (eq (first type) :if)))
                  (logbitp (third type) (getf plist (cl-ton::tl-field-key (second type)) 0)))
          (setf plist (append plist (list key (%fuzz-value type plist depth classes)))))))
    (apply #'cl-ton::tl-make (cl-ton::tl-con-name con) plist)))

(defun %tl-equal (a b)
  (cond ((and (cl-ton::tl-obj-p a) (cl-ton::tl-obj-p b))
         (and (string= (cl-ton::tl-obj-name a) (cl-ton::tl-obj-name b))
              (let ((fa (cl-ton::tl-obj-fields a)) (fb (cl-ton::tl-obj-fields b)))
                (and (= (length fa) (length fb))
                     (loop for (k v) on fa by #'cddr
                           always (and (cl-ton::tl-plist-has-key-p fb k) (%tl-equal v (getf fb k))))))))
        ((and (vectorp a) (vectorp b) (not (stringp a)) (not (typep a '(vector (unsigned-byte 8)))))
         (and (= (length a) (length b)) (every #'%tl-equal a b)))
        ((and (listp a) (vectorp b) (not (stringp b))) (%tl-equal (coerce a 'vector) b))
        ((typep a '(vector (unsigned-byte 8))) (equalp a b))
        (t (equal a b))))

(defun test-tl-schema-is-the-vendored-files ()
  (format t "binary TL schema: the registry is exactly lite_api.tl + ton_api.tl~%")
  (let* ((vendored (remove-duplicates (append (%vendored-names "ton_api.tl") (%vendored-names "lite_api.tl"))
                                      :test #'equal))
         (names (remove-duplicates (mapcar #'car vendored) :test #'string=)))
    (check "the vendored schema files are the pinned revision (sha256)"
           (every (lambda (pin)
                    (let ((actual (cl-ton:octets->hex (cl-ton:sha256 (%slurp (%tl-file (car pin)))))))
                      (or (string-equal actual (cdr pin))
                          (progn (format t "    ~A is ~A~%" (car pin) actual) nil))))
                  *vendored-schema-sha256*))
    (check "no name is declared twice with different text (the files agree where they overlap)"
           (= (length vendored) (length names)))
    (check (format nil "the registry holds exactly the ~D vendored constructors, no more" (length names))
           (and (= (hash-table-count cl-ton::*tl-by-name*) (length names))
                (= (hash-table-count cl-ton::*tl-by-id*) (length names))
                (every (lambda (n) (gethash n cl-ton::*tl-by-name*)) names)))
    (check "...each with the vendored declaration text"
           (every (lambda (v)
                    (string= (cdr v) (cl-ton::tl-con-declaration (gethash (car v) cl-ton::*tl-by-name*))))
                  vendored))
    (check "the language builtins (int, long, bytes, vector, ...) are types, not constructors"
           (notany (lambda (n) (gethash n cl-ton::*tl-by-name*)) cl-ton::*tl-builtin-names*))
    (check "explicit #ids are the wire ids (they differ from the CRC where the declaration grew)"
           (every (lambda (p) (= (cl-ton::tl-id-of (first p)) (second p))) *explicit-id-constructors*))
    (check "...and the newer liteServer.transactionId carries its metadata field behind mode bit 8"
           (equal (cdr (assoc "metadata" (cl-ton::tl-con-fields (cl-ton::tl-find-con "liteServer.transactionId"))
                              :test #'string=))
                  '(:if "mode" 8 (:bare "liteServer.transactionMetadata"))))
    (check "ids are unique and a conflicting declaration is refused, leaving the registry intact"
           (let ((id (cl-ton::tl-id-of "liteServer.getTime")))
             (and (%signals ton-error (cl-ton::tl-register "liteServer.getTime x:int = liteServer.CurrentTime"))
                  (= id (cl-ton::tl-id-of "liteServer.getTime"))
                  (null (cl-ton::tl-con-fields (cl-ton::tl-find-con "liteServer.getTime"))))))))

(defun test-tl-roundtrip-every-constructor ()
  (format t "binary TL schema: every constructor round-trips; garbage is only ever rejected~%")
  (let ((classes (%class-members)) (tested 0) (gave-up '()) (failed '()))
    (maphash
     (lambda (name con)
       (handler-case
           (dotimes (round 3)
             (let* ((obj (%fuzz-object con 0 classes))
                    (octets (cl-ton::tl-encode obj))
                    (back (cl-ton::tl-decode octets)))
               (unless (and (%tl-equal obj back) (equalp octets (cl-ton::tl-encode back)))
                 (push name failed))))
         (%fuzz-gave-up () (push name gave-up))
         (error (e) (push (format nil "~A: ~A" name e) failed)))
       (incf tested))
     cl-ton::*tl-by-name*)
    (check (format nil "~D constructors, 3 random values each: decode(encode(x)) = x and re-encoding is byte-identical (failed: ~S)"
                   tested (subseq failed 0 (min 5 (length failed))))
           (null failed))
    (check (format nil "...none had to be skipped (~S)" gave-up) (null gave-up)))
  (let ((ids (loop for id being the hash-keys of cl-ton::*tl-by-id* collect id)) (bad '()) (rejected 0) (accepted 0))
    (dotimes (i 4000)
      (let* ((id (nth (%rnd (length ids)) ids))
             (tail (%rnd-octets (%rnd 80)))
             (octets (concatenate '(simple-array (unsigned-byte 8) (*)) (%id-le id) tail)))
        (handler-case (progn (cl-ton::tl-decode octets) (incf accepted))
          (cl-ton::tl-decode-error () (incf rejected))
          (error (e) (push (format nil "~8,'0X: ~A" id e) bad)))))
    (check (format nil "4000 garbage inputs behind real constructor ids: ~D rejected cleanly, ~D happened to parse, ~D crashed (~S)"
                   rejected accepted (length bad) (subseq bad 0 (min 3 (length bad))))
           (null bad))))

(defun test-tlapi ()
  (test-tlapi-schema)
  (test-tlapi-validation)
  (test-tlapi-json-bridge)
  (test-tl-schema-is-the-vendored-files)
  (test-tl-roundtrip-every-constructor)
  (test-tlapi-vs-tonlib))
