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

; When we compile and load shared libraries, we'll stick them into a registry
; so we know what they are and that they're already available.

(defstruct llvm-registry-entry
  ;; Single entry in the registry of LLVM libraries
  (asm)   ;; The llvmasm object
  (lisp-fn)    ;; Name of the Lisp function we've generated (a gensym)
  )

(defparameter *llvm-asm-registry*
  ;; Binds fnname to its registry entry.
  (make-hash-table))



; TODO:
;;  -- set up llvm-load-shared-library to gensym a lisp function name
;;     and installs the thing into the registry (based on code that works below)
;;  -- add new function that lets you run an assembly by looking up its
;;     name in the registry and applying it to some stobj arrays


(defun llvm-load-shared-library (tmpdir asm state)
  "Returns (mv errmsg? state)"
  (unless (acl2::live-state-p state)
    (error "llvm-load-shared-library requires a live state."))

  (let* ((fnname (llvmasm->fnname asm))
         (look   (gethash fnname *llvm-asm-registry*)))
    (cond (look
           (if (equal look asm)
               (mv nil state)
             (mv (msg "Error: name ~s0 already in use." fnname) state)))
          (let* ((libfnname    (str::cat "lib" asm.fnname))
                 (libfnname.so (str::cat "lib" asm.fnname ".so"))
                 (lisp-fn      (gensym))
                 (entry        (make-llvm-registry-entry :asm asm :lisp-fn lisp-fn)))
            (handler-case
              (progn
                (let ((cffi:*foreign-library-directories* (list tmpdir)))
                  (cffi:use-foreign-library libfnname)
                  (cffi:defcfun (fnname fn) :void (ins (:pointer int64)) (outs (:pointer int64)))
                  
                (mv nil state))
              (error (condition)
                     (let ((condition-str (format nil "~a" condition)))
                       (mv (msg "Error loading ~s0: ~s1" libfnname.so condition-str)
                           state))))))


;; code that works:::

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





