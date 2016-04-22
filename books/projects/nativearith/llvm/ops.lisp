; Native Arithmetic Library
; Copyright (C) 2015-2016 Kookamara LLC
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
(include-book "../smallops")
(include-book "centaur/quicklisp/cffi" :dir :system)
(include-book "std/util/defconsts" :dir :system)
; (depends-on "ops-raw.lsp")
; (depends-on "libnarith_ops.so")

(defxdoc llvm-smallops
  :parents (nativearith)
  :short "The LLVM counterparts of our ACL2 @(see smallops), and a basic way
to test them."

  :long "<p>Each of our @(see smallops) has a corresponding definition in LLVM
assembly code.  To try to ensure the correspondence of these definitions, we
arrange so that we can call the LLVM functions from within ACL2 and at least
run basic tests on them.</p>

<p>In brief, the basic mechanism is:</p>

<ul>

<li>We compile the LLVM definitions into a standalone shared library,
@('libnarith_ops').</li>

<li>We load this library into ACL2 using the <a
href='https://common-lisp.net/project/cffi/'>CFFI</a> foreign function
interfacing library.</li>

<li>For each operation @('foo'), the corresponding LLVM definition gets named
@('narith-foo').  For instance, for @(see i64eql) we have @(see
narith-i64eql).</li>

<li>We run some basic tests to ensure that each of these LLVM definitions
corresponds to its ACL2 definition; see the file
@('nativearith/llvm/opstest').</li>

</ul>")

(local (xdoc::set-default-parents llvm-smallops))

(defconsts *narith-llvm-directory* (cbd))


(define load-narith (&key (state 'state))
  :returns (mv (errmsg "NIL on success or an error message on failure.")
               state)
  :short "Load a shared library with the LLVM versions of the nativearith
          @(see smallops)."
  :long "<p>Logically this is just an oracle read.  Normally there should be no
         reason to call this explicitly because we automatically run it
         whenever the @('ops.lisp') book is loaded.</p>"
  (progn$
   (raise "Raw lisp definition not installed?")
   (b* (((mv ?er val state) (read-acl2-oracle state)))
     (mv val state))))


(defmacro def-narith-op (name args)
  `(define ,(intern$ (str::cat "NARITH-" (symbol-name name)) "NATIVEARITH") ,args
     :parents (,name llvm-smallops)
     :returns (ans)
     :short ,(cat "Native LLVM counterpart to @(see " (xdoc::full-escape-symbol name) ").")
     :long "<p>This function should be redefined ``under the hood'' when the
            @('libnarith_ops') library is loaded.  We cause an error in the
            logical definition only in case this somehow doesn't occur.</p>"
     :enabled t
     :split-types t
     (progn$ (raise "LLVM definition not installed?")
             (,name . ,(strip-cars args)))))


(def-narith-op i64bitnot ((a i64-p :type (signed-byte 64))))
(def-narith-op i64sminus ((a i64-p :type (signed-byte 64))))
(def-narith-op i64logcar ((a i64-p :type (signed-byte 64))))
(def-narith-op i64logcdr ((a i64-p :type (signed-byte 64))))

(def-narith-op i64eql    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64neq    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))

(def-narith-op i64sle    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64slt    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64sge    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64sgt    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))

(def-narith-op i64ule    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64ult    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64uge    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64ugt    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))

(def-narith-op i64bitand     ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64bitor      ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64bitxor     ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64loghead    ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64logext     ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64shl        ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64shr        ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))

(def-narith-op i64plus       ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64upluscarry ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64minus      ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64times      ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))

(def-narith-op i64sdiv   ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))
(def-narith-op i64udiv   ((a i64-p :type (signed-byte 64)) (b i64-p :type (signed-byte 64))))

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
