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
(include-book "i64")
(include-book "util")
(include-book "std/util/defprojection" :dir :system)
(local (std::add-default-post-define-hook :fix))

(defflexsum smallvar
  :parents (smallexpr)
  :kind nil
  (:smallvar
   :short "Represents a single variable."
   :type-name smallvar
   :cond t
   :shape (if (atom x)
              (or (stringp x)
                  (and (symbolp x)
                       (not (booleanp x))))
            (and (eq (car x) :smallvar)
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
     (hons :smallvar (hons name subscripts)))
   :long "<p>Think of variables as simple structs with a @('name') and
@('subscripts'), where the name can be any ACL2 object.  These subscripts have
<b>no special meaning</b> and are only intended to be a convenient way to
distinguish variables from one another.  That is, if two variables have the
same name but different subscripts, then we think of them as being two
completely different variables with no special relationship to one another.</p>

<p>Our variables are always honsed.  Variables with simple names (strings or
non-boolean symbols) and no subscripts are represented just with their name.
Variables with more complex names or subscripts are represented essentially as
@('(:var name . subscripts)').</p>"))

(deflist smallvarlist
  :elt-type smallvar
  :true-listp t
  :elementp-of-nil nil)

(deftypes smallexpr
  :prepwork
  ((local (defthm smallvar-p-of-quote
            (equal (smallvar-p (cons 'quote x))
                   nil)
            :hints(("Goal" :in-theory (enable smallvar-p)))))
   (local (defthm smallvar-p-of-fncall
            (implies (fn-p fn)
                     (equal (smallvar-p (cons fn args))
                            nil))
            :hints(("Goal" :in-theory (enable fn-p smallvar-p))))))

  (defflexsum smallexpr
    :parents (nativearith)
    :short "Represents a single, ``small'' (64-bit) inteeger expression."
    (:var
     :short "A variable."
     :cond (or (atom x)
               (smallvar-p x))
     :fields ((var :acc-body x :type smallvar-p))
     :ctor-body var
     :count-incr 2)
    (:const
     :short "A quoted constant."
     :cond (eq (car x) 'quote)
     :shape (and (consp (cdr x))
                 (i64-p (second x))
                 (not (cddr x)))
     :fields ((val :acc-body (second x) :type i64))
     :ctor-body (hons 'quote (hons val nil))
     :count-incr 1)
    (:call
     :short "A function applied to some expressions."
     :fields ((fn   :acc-body (car x) :type fn)
              (args :acc-body (cdr x) :type smallexprlist))
     :ctor-body (hons fn args))
    :long "<p>This is our basic expression type for ``native'' machine-like
           arithmetic.  Our expressions are either variables, constants, or
           functions applied to some arguments.  They are always honsed.</p>")

  (deflist smallexprlist
    :elt-type smallexpr
    :true-listp t))

(defthm smallexprlist-count-of-args
  (< (smallexprlist-count (smallexpr-call->args x))
     (smallexpr-count x))
  :rule-classes :linear
  ;; Gross hints, but it's nice for the count to unconditionally decrease
  ;; when we visit the arguments to an expression.
  :hints(("Goal" :in-theory (enable smallexpr-count
                                    smallexprlist-count
                                    smallexpr-kind
                                    smallvar-p
                                    smallexpr-call->args))))


(define smallexprs-from-smallvars ((x smallvarlist-p))
  :returns (exprs smallexprlist-p)
  :parents (smallexprlist)
  :short "Identity function for converting @(see smallvar)s into @(see smallexpr)s."
  :inline t
  (mbe :logic (if (atom x)
                  nil
                (cons (make-smallexpr-var :var (car x))
                      (smallexprs-from-smallvars (cdr x))))
       :exec x)
  :prepwork
  ((local (in-theory (enable smallexpr-p
                             smallexpr-kind
                             smallexpr-var->var)))))

(defsection smallexprs-from-smallvars-thms
  :extension (smallexprs-from-smallvars)

  (defprojection smallexprs-from-smallvars (x)
    :already-definedp t
    (make-smallexpr-var :var x)))

