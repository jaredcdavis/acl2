; Chess in ACL2
; Copyright (C) 2014 Kookamara LLC
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

(in-package "CHESS")
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/lists/top" :dir :system)
(local (std::add-default-post-define-hook :fix))

(define nth-loose ((n natp) x)
  :enabled t
  (mbe :logic (nth n x)
       :exec (if (atom x)
                 nil
               (if (zp n)
                   (car x)
                 (nth-loose (- n 1) (cdr x))))))

(define update-nth-loose ((n natp) val x)
  :enabled t
  :prepwork ((local (in-theory (disable acl2::update-nth-when-atom))))
  (mbe :logic (update-nth n val x)
       :exec (if (zp n)
                 (cons val (and (consp x) (cdr x)))
               (let ((x (and (consp x) x)))
                 (cons (car x)
                       (update-nth-loose (1- n) val (cdr x)))))))

