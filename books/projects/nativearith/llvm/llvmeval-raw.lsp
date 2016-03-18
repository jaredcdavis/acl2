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

(include-book "centaur/quicklisp/cffi" :dir :system)

:q

;; (cffi:define-foreign-library libops
;;                              (:unix (:or "libnarith_ops.so"))
;;                              (t (:default "libnarith_ops")))

;; (let ((cffi:*foreign-library-directories*
;;        (list "/home/jared/xb/acl2/books/projects/nativearith/llvm/")))
;;   (cffi:use-foreign-library libops))


;; (cffi:define-foreign-library libfoo
;;                              (:unix "libfoo.so")
;;                              (t (:default "libfoo")))

;; (let ((cffi:*foreign-library-directories*
;;        (list "/home/jared/xb/acl2/books/projects/nativearith/llvm/narith_tmp/")))
;;   (cffi:use-foreign-library libfoo))

;; cool this works!

;; We can probably avoid this memcpy overhead -- look at the CFFI manual's section
;; on "optimizing type translators".

(let ((cffi:*foreign-library-directories*
       (list "/home/jared/xb/acl2/books/projects/nativearith/llvm/narith_tmp/")))
  (cffi:use-foreign-library "libfoo.so")
  (cffi:defcfun ("foo" my-foo)
                :void
                (ins (:pointer :int64))
                (outs (:pointer :int64))))

(defparameter *ins* (cffi:foreign-alloc :int64  :initial-contents #(1 2 3 4)))
(defparameter *outs* (cffi:foreign-alloc :int64 :initial-contents #(9 8 7 6)))

(defun load-foreign-array-aux (ptr len acc)
  (if (zp len)
      acc
    (let* ((len (- len 1))
           (acc (cons (cffi:mem-aref ptr :int64 len) acc)))
      (load-foreign-array-aux ptr len acc))))

(defun load-foreign-array (ptr len)
  (load-foreign-array-aux ptr len nil))

(load-foreign-array *ins* 4)
(load-foreign-array *outs* 4)

(my-foo *ins* *outs*)

(load-foreign-array *ins* 4)
(load-foreign-array *outs* 4)



;; (defun llvm-load-shared-library (asm)
;;   "Returns (mv errmsg? state)"
;;   (b* (((llvmasm asm))
;;        (libfnname    (str::cat "lib" asm.fnname))
;;        (libfnname.so (str::cat "lib" asm.fnname ".so")))
;;     (handler-case
;;       (progn
;;         (let ((cffi:*foreign-library-directories* (list "./narith_tmp")))
;;           (cffi:use-foreign-library libfnname))
;;         (mv nil state))
;;       (error (condition)
;;              (let ((condition-str (format nil "~a" condition)))
;;                (mv (msg "Error loading ~s0: ~s1" libfnname.so condition-str)
;;                    state))))))


