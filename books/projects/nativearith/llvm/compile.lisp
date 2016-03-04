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
(include-book "../smallexpr")
(include-book "../smallvars")
(include-book "std/util/defconsts" :dir :system)
(local (include-book "oslib/catpath" :dir :system))
(local (include-book "std/io/read-file-characters" :dir :system))
; (depends-on "ops.ll")

(defsection *ops.ll*
  :parents (llvm-smallops)
  :short "LLVM assembly code definitions of the LLVM operations."
  :long "@(def *ops.ll*)"

  (defconsts (*ops.ll* state)
    (acl2::read-file-as-string (oslib::catpath (cbd) "ops.ll") state)))



(defxdoc smallexpr-to-llvm
  :parents (nativearith)
  :short "Compiler from small expressions into LLVM assembly code.")


;; We can probably mostly style this after AIG2C
;
;  -- would be nice to have a sense of how this would work, end-to-end, with a C interface, for instance.
;
; We need to be able to generate a top-level function; what's its signature?
;
;  - probably it should take something like an array of 64-bit integers, which are the inputs.
;  - probably it should write its results to an array of 64-bit integers, of the right size.
;
; This would be relatively easy to drop into a C harness.
;   -- It would make variable translation straightforward.
;
; Yep, LLVM assembly supports an array type.
; OK, demo.ll resolves a lot of the open questions
;
;   -- it's definitely better to bundle related operations together instead of
;      doing all the loads, all the operations, then all the stores.  so we
;      probably want a notion of nodes that we have already computed versus
;      nodes that need to be emitted still.
;
;   -- it's definitely better to handle branching in an explicit way.  we
;      probably should add an ITE operator that is explicitly lazy, and then
;      arrange to compile it by sort of hoisting up common subexpressions, then
;      doing an explicit branch to separate blocks with custom instructions,
;      each of which reconverge to a finishing block.






