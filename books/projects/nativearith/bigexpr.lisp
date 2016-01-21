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
(include-book "bigint")
(include-book "smallexpr")

(deftypes bigexpr
  :prepwork
  ((local (defthm var-p-of-quote
            (equal (var-p (cons 'quote x))
                   nil)
            :hints(("Goal" :in-theory (enable var-p)))))
   (local (defthm var-p-of-fncall
            (implies (fn-p fn)
                     (equal (var-p (cons fn args))
                            nil))
            :hints(("Goal" :in-theory (enable fn-p var-p))))))

  (defflexsum bigexpr
    :parents (nativearith)
    :short "A @(see bigint) arithmetic expression."
    (:var
     :short "A variable."
     :cond (or (atom x)
               (var-p x))
     :fields ((name :acc-body x :type var-p))
     :ctor-body name
     :long "<p>For now we reuse the representation of variables from ordinary
            @(see expr)s.  BOZO it might be better to arrange so that expr vars
            have an extra level of indexing, so that we can just assign the
            blocks of a bigexpr var to successive use successive indices of
            some base variable.</p>")
    (:const
     :short "A quoted constant."
     :cond (eq (car x) 'quote)
     :shape (and (consp (cdr x))
                 (bigint-p (second x))
                 (not (cddr x)))
     :fields ((val :acc-body (second x) :type bigint-p))
     :ctor-body (hons 'quote (hons val nil)))
    (:call
     :short "A function applied to some expressions."
     :fields ((fn   :acc-body (car x) :type fn)
              (args :acc-body (cdr x) :type bigexprlist))
     :ctor-body (hons fn args)))

  (deflist bigexprlist
    :elt-type bigexpr
    :true-listp t))
