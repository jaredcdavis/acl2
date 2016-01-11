; Native Arithmetic Library
; Copyright (C) 2015 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "NATIVEARITH")
(include-book "../i64ops")
(include-book "centaur/quicklisp/cffi" :dir :system)
(include-book "std/util/defconsts" :dir :system)
; (depends-on "ops-raw.lsp")
; (depends-on "libnarith_ops.so")

(defxdoc narith-ops-llvm
  :parents (nativearith)
  :short "ACL2 foreign function interface to the narith_ops library."
  :long "<p>To try to ensure the correspondence between our LLVM definitions
and the logical definitions of our @(see i64ops), we arrange so that we can
call the LLVM functions from within ACL2 and at least run basic tests on
them.</p>")

(local (xdoc::set-default-parents narith-ops-llvm))

(defconsts *narith-llvm-directory* (cbd))


(define load-narith (&key (state 'state))
  :returns (mv (errmsg "NIL on success or an error message on failure.")
               state)
  :short "Load a shared library with the LLVM versions of the nativearith
          operations."
  :long "<p>Logically this is just an oracle read.  Normally there should be no
         reason to call this explicitly because we automatically run it
         whenever the @('ops.lisp') book is loaded.</p>"
  (progn$
   (raise "Raw lisp definition not installed?")
   (b* (((mv ?er val state) (read-acl2-oracle state)))
     (mv val state))))


(defmacro def-narith-op (name args)
  `(define ,(intern$ (str::cat "NARITH-" (symbol-name name)) "NATIVEARITH") ,args
     :short ,(cat "Native LLVM counterpart to @(see " (xdoc::full-escape-symbol name) ")")
     :enabled t
     (progn$ (raise "LLVM definition not installed?")
             (,name . ,(strip-cars args)))))

(def-narith-op i64eql    ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
(def-narith-op i64neq    ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
;(def-narith-op i64sle    ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
;(def-narith-op i64slt    ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
;(def-narith-op i64sge    ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
;(def-narith-op i64sgt    ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
(def-narith-op i64bitand ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
(def-narith-op i64bitor  ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
(def-narith-op i64bitxor ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
(def-narith-op i64plus   ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
(def-narith-op i64minus  ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
(def-narith-op i64times  ((a :type (signed-byte 64)) (b :type (signed-byte 64))))
;(def-narith-op i64sdiv   ((a :type (signed-byte 64)) (b :type (signed-byte 64))))

(defttag :nativearith.llvm)

(acl2::include-raw "ops-raw.lsp" :host-readtable t)

(make-event
 (b* (((mv errmsg state) (load-narith))
      ((when errmsg)
       (er soft 'load-narith "~@0" errmsg)))
   (value `(value-triple :invisible)))
 :check-expansion t)

(local (include-book "misc/assert" :dir :system))
(local
 (progn
   (assert! (equal (narith-i64eql 3 3) 1))
   (assert! (equal (narith-i64eql 3 4) 0))))
