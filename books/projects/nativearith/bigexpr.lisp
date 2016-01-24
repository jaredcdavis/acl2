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
(include-book "util")

(defflexsum bigvar
  :parents (bigexpr)
  :kind nil
  (:bigvar
   :short "Represents a single variable."
   :type-name bigvar
   :cond t
   :shape (if (atom x)
              (or (stringp x)
                  (and (symbolp x)
                       (not (booleanp x))))
            (and (eq (car x) :bigvar)
                 (consp (cdr x))
                 (not (and (or (stringp (cadr x))
                               (and (symbolp (cadr x))
                                    (not (booleanp (cadr x)))))
                           (not (cddr x))))))
   :fields
   ((name :acc-body (if (atom x)
                        x
                      (cadr x))
          :doc "The name of this variable.  This can be any ACL2 object at all,
                but our representation is optimized for @(see stringp) or @(see
                symbolp) names.")
    (subscripts :type nat-listp
                :acc-body (if (atom x) nil (cddr x))
                :default nil
                :doc "An list of natural valued ``subscripts'' for this
                      variable.  Variables with the same name but different
                      subscripts are regarded as distinct."))
   :ctor-body
   (if (and (or (stringp name)
                (and (symbolp name)
                     (not (booleanp name))))
            (not subscripts))
       (hons-copy name)
     (hons :bigvar (hons name subscripts)))
   :long "<p>This is virtually identical to a @(see smallvar), but having them
as two separate types helps to keep tabs of which kind of variables we are
working with.</p>"))

(deftypes bigexpr
  :prepwork
  ((local (defthm bigvar-p-of-quote
            (equal (bigvar-p (cons 'quote x))
                   nil)
            :hints(("Goal" :in-theory (enable bigvar-p)))))
   (local (defthm bigvar-p-of-fncall
            (implies (fn-p fn)
                     (equal (bigvar-p (cons fn args))
                            nil))
            :hints(("Goal" :in-theory (enable fn-p bigvar-p))))))

  (defflexsum bigexpr
    :parents (nativearith)
    :short "A @(see bigint) arithmetic expression."
    (:var
     :short "A variable."
     :cond (or (atom x)
               (bigvar-p x))
     :fields ((name :acc-body x :type bigvar-p))
     :ctor-body name)
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
    :true-listp t
    :elementp-of-nil nil))
