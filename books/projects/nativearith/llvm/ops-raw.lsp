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

(defun load-narith-fn (state)
  (unless (acl2::live-state-p state)
    (error "LOAD-NARITH can only be called on a live state."))
  (cffi:define-foreign-library libnarith_ops
                               (:unix (:or "libnarith_ops.so"))
                               (t (:default "libnarith_ops")))
  (handler-case
    (progn
      (let ((cffi:*foreign-library-directories* (list *narith-llvm-directory*)))
        (cffi:use-foreign-library libnarith_ops))
      (mv nil state))
    (error (condition)
           (let ((condition-str (format nil "~a" condition)))
             (mv (msg "Error loading nativearith LLVM operations: ~s0" condition-str)
                 state)))))

(cffi:defcfun "narith_i64eql"    :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64neq"    :int64 (a :int64) (b :int64))

(cffi:defcfun "narith_i64sle"    :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64slt"    :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64sge"    :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64sgt"    :int64 (a :int64) (b :int64))

(cffi:defcfun "narith_i64ule"    :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64ult"    :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64uge"    :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64ugt"    :int64 (a :int64) (b :int64))

(cffi:defcfun "narith_i64bitnot" :int64 (a :int64))
(cffi:defcfun "narith_i64sminus" :int64 (a :int64))
(cffi:defcfun "narith_i64logcar" :int64 (a :int64))
(cffi:defcfun "narith_i64logcdr" :int64 (a :int64))

(cffi:defcfun "narith_i64bitand"     :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64bitor"      :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64bitxor"     :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64loghead"    :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64logext"     :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64shl"        :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64lshr"       :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64ashr"       :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64plus"       :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64upluscarry" :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64minus"      :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64times"      :int64 (a :int64) (b :int64))

(cffi:defcfun "narith_i64sdiv"   :int64 (a :int64) (b :int64))
(cffi:defcfun "narith_i64udiv"   :int64 (a :int64) (b :int64))


