; Native Arithmetic Library
; Copyright (C) 2015 Kookamara LLC
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
(include-book "ops")
(include-book "centaur/fty/deftypes" :dir :system)
(local (std::add-default-post-define-hook :fix))

(defflexsum var
  :parents (expr)
  :kind nil
  (:var
   :short "Represents a single variable."
   :type-name var
   :cond t
   :shape (if (atom x)
              (or (stringp x)
                  (and (symbolp x)
                       (not (booleanp x))))
            (and (eq (car x) :var)
                 (consp (cdr x))
                 (not (and (or (stringp (cadr x))
                               (and (symbolp (cadr x))
                                    (not (booleanp (cadr x)))))
                           (eql (cddr x) 0)))))
   :fields
   ((name :acc-body (if (atom x)
                        x
                      (cadr x))
          :doc "The name of this variable.  This can be any ACL2 object at all,
                but our representation is optimized for @(see stringp) or @(see
                symbolp) names.")
    (index :type natp
           :acc-body (if (atom x) 0 (cddr x))
           :default 0
           :doc "An natural valued index for this variable.  The default
                 index (which enjoys an optimized representation) is 0."))
   :ctor-body
   (if (and (or (stringp name)
                (and (symbolp name)
                     (not (booleanp name))))
            (eql index 0))
       (hons-copy name)
     (hons :var (hons name index)))
   :long "<p>Think of variables as simple structs with a @('name') and
@('index'), where the name can be any ACL2 object.  These indices have <b>no
special meaning</b> and are only intended to be a convenient way to distinguish
variables from one another.  That is, if two variables have the same name but
different indices, then we think of them as being two completely different
variables.</p>

<p>Our variables are always honsed.  Variables with simple names (strings or
non-boolean symbols) and index 0 are represented as just their name.  Variables
with more complex names or positive indices are represented essentially as
@('(:var name . index)').</p>"))


(defsection fn
  :parents (expr)
  :short "Represents a valid function name."
  :long "<p>Syntactically, we allow most symbols to be used as function names.
However, our expression language is fixed: only a few certain pre-defined @(see
operations) are actually understood.</p>"
  :autodoc nil
  (local (xdoc::set-default-parents fn))

  (define fn-p (x)
    :short "Recognizer for valid @(see fn)s."
    (and (symbolp x)
         (not (eq x 'quote))
         (not (keywordp x)))
    ///
    (defthm fn-p-compound-recognizer
      (implies (fn-p x)
               (symbolp x))
      :rule-classes :compound-recognizer))

  (define fn-fix (x)
    :short "Fixing function for @(see fn)s."
    :returns (x fn-p)
    (if (fn-p x)
        x
      'id)
    ///
    (defthm fn-fix-when-fn-p
      (implies (fn-p x)
               (equal (fn-fix x) x))))

  (defsection fn-equiv
    :short "Equivalence relation for @(see fn)s."
    (deffixtype fn
      :pred fn-p
      :fix fn-fix
      :equiv fn-equiv
      :define t
      :forward t
      :equal eq)))


(deftypes expr
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

  (defflexsum expr
    :parents (nativearith)
    :short "Represents a single expression."
    (:var
     :short "A variable."
     :cond (or (atom x)
               (var-p x))
     :fields ((name :acc-body x :type var-p))
     :ctor-body name)
    (:const
     :short "A quoted constant."
     :cond (eq (car x) 'quote)
     :shape (and (consp (cdr x))
                 (i64-p (second x))
                 (not (cddr x)))
     :fields ((val :acc-body (second x) :type i64))
     :ctor-body (hons 'quote (hons val nil)))
    (:call
     :short "A function applied to some expressions."
     :fields ((fn   :acc-body (car x) :type fn)
              (args :acc-body (cdr x) :type exprlist))
     :ctor-body (hons fn args))
    :long "<p>This is our basic expression type.  Our expressions are either
           variables, constants, or functions applied to some arguments.  They
           are always honsed.</p>")

  (deflist exprlist
    :elt-type expr
    :true-listp t))
