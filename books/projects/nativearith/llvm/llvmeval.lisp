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
(include-book "exprs-to-llvm")
(include-book "centaur/misc/tshell" :dir :system)
(include-book "std/io/base" :dir :system)
(include-book "oslib/catpath" :dir :system)
(include-book "centaur/quicklisp/cffi" :dir :system)

(defconst *asm*
  (smallexprs-to-llvm-top "foo"
                          (list '(i64eql a b)
                                '(i64plus a (i64bitand b c)))))

(define llvm-load-shared-library ((tmpdir stringp)
                                  (asm    llvmasm-p)
                                  state)
  :returns (mv (errmsg (or (stringp errmsg)
                           (not errmsg))
                       :rule-classes :type-prescription)
               state)
  (declare (ignorable tmpdir asm))
  (progn$ (raise "Under the hood definition not yet installed.")
          (b* (((mv ?er val state) (read-acl2-oracle state)))
            (mv (if (stringp val)
                    val
                  nil)
                state))))

; (depends-on "llvmeval-raw.lsp")
(defttag :llvmeval)
(acl2::include-raw "llvmeval-raw.lsp" :host-readtable t)

(define llvm-load-compiled ((asm llvmasm-p) state)
  :returns (mv (okp booleanp :rule-classes :type-prescription)
               state)
  (b* (((llvmasm asm))

       (cbd           (cbd))
       (tmpdir        (oslib::catpath cbd "narith_tmp"))
       (fnname.ll     (oslib::catpath tmpdir (str::cat asm.fnname ".ll")))
       (fnname.ll.opt (oslib::catpath tmpdir (str::cat asm.fnname ".ll.opt")))
       (fnname.s      (oslib::catpath tmpdir (str::cat asm.fnname ".s")))
       (fnname.o      (oslib::catpath tmpdir (str::cat asm.fnname ".o")))
       (libfnname.so  (oslib::catpath tmpdir (str::cat "lib" asm.fnname ".so")))

       (- (cw "*** Writing ~s0~%" fnname.ll))
       ((mv channel state) (open-output-channel fnname.ll :character state))
       ((unless channel)
        (raise "Error opening ~x0 for writing~%" channel)
        (mv nil state))
       (state (princ$ asm.code channel state))
       (state (close-output-channel channel state))

       (- (cw "*** Optimizing ~s0 into ~s1~%" fnname.ll fnname.ll.opt))
       (- (acl2::tshell-ensure))
       ((mv status ?lines)
        (acl2::tshell-call (str::cat "opt -O3 " fnname.ll " -o=" fnname.ll.opt)))
       ((unless (eql status 0))
        (raise "Error running opt on ~x0~%" fnname.ll)
        (mv nil state))

       (- (cw "*** Compiling ~s0 into ~s1~%" fnname.ll.opt fnname.s))
       ((mv status ?lines)
        (acl2::tshell-call (str::cat "llc -o " fnname.s " " fnname.ll.opt)))
       ((unless (eql status 0))
        (raise "Error running llc on ~x0~%" fnname.ll.opt)
        (mv nil state))

       (- (cw "*** Assembling ~s0 into ~s1~%" fnname.s fnname.o))
       ((mv status ?lines)
        (acl2::tshell-call (str::cat "as " fnname.s " -o " fnname.o)))
       ((unless (eql status 0))
        (raise "Error running llc on ~x0~%" fnname.ll.opt)
        (mv nil state))

       (- (cw "*** Converting ~s0 into ~s1~%" fnname.o libfnname.so))
       ((mv status ?lines)
        (acl2::tshell-call (str::cat "clang -shared " fnname.o " -o " libfnname.so)))
       ((unless (eql status 0))
        (raise "Error running clang on ~x0~%" fnname.o)
        (mv nil state))

       (- (cw "*** Loading ~s0 into ACL2.~%" libfnname.so))
       ((mv errmsg state)
        (llvm-load-shared-library asm state))
       ((when errmsg)
        (raise "~s0" errmsg)
        (mv nil state)))

    (mv t state)))

(llvm-load-compiled *asm* state)

