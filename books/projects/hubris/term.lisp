; Hubris - Meta prover for ACL2
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

(in-package "HUBRIS")
(include-book "std/util/defval" :dir :system)
(include-book "std/misc/two-nats-measure" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (include-book "std/lists/take" :dir :system))
(std::add-default-post-define-hook :fix)

(defun hons-list-macro (lst)
  (declare (xargs :mode :program
                  :guard (true-listp lst)))
  (if (atom lst)
      nil
    `(hons ,(car lst)
           ,(hons-list-macro (cdr lst)))))

(defmacro hons-list (&rest args)
  (hons-list-macro args))

(defxdoc terms
  :parents (hubris)
  :short "Term representation.")

(local (set-default-parents terms))

(define variable-p (x)
  :returns bool
  (symbolp x)
  ///
  (defthm variable-p-compound-recognizer-weak
    (implies (variable-p x)
             (atom x))
    :rule-classes :compound-recognizer))

(define variable-fix ((x variable-p))
  :parents (variable-p)
  :prepwork ((local (in-theory (enable variable-p))))
  :returns (x-fix variable-p)
  :inline t
  (mbe :logic (if (variable-p x)
                  x
                nil)
       :exec x)
  ///
  (defthm variable-fix-when-variable-p
    (implies (variable-p x)
             (equal (variable-fix x)
                    x))))

(deffixtype variable
  :pred variable-p
  :fix variable-fix
  :equiv variable-equiv
  :forward t
  :define t)

(deflist variablelist
  :elt-type variable)


(defval *nil*
  :parents (constant-p)
  :short "Formal @(see constant-p) for @('nil')."
  (hons 'quote (hons nil nil)))

(define constant-p (x)
  :returns bool
  (and (consp x)
       (consp (cdr x))
       (eq (car x) 'quote)
       (not (cddr x)))
  ///
  (defthm constant-p-compound-recognizer-weak
    (implies (constant-p x)
             (consp x))
    :rule-classes :compound-recognizer))

(define constant-fix ((x constant-p))
  :parents (constant-p)
  :prepwork ((local (in-theory (enable constant-p))))
  :returns (x-fix constant-p)
  :inline t
  (mbe :logic (if (constant-p x)
                  x
                *nil*)
       :exec x)
  ///
  (defthm constant-fix-when-constant-p
    (implies (constant-p x)
             (equal (constant-fix x)
                    x))))

(deffixtype constant
  :pred constant-p
  :fix constant-fix
  :equiv constant-equiv
  :forward t
  :define t)

(define constant (x)
  :parents (constant-p)
  :short "Create a formal constant, similar to @('quote')."
  :returns (const constant-p)
  :prepwork ((local (in-theory (enable constant-p))))
  (hons 'quote (hons x nil)))

(define constant->val ((x constant-p))
  :prepwork ((local (in-theory (enable constant-p constant constant-fix))))
  :verbosep t
  (second (constant-fix x))
  ///
  (defthm constant->val-of-constant
    (equal (constant->val (constant x))
           x)))



(define funname-p (x)
  :returns bool
  (symbolp x)
  ///
  (defthm funname-p-compound-recognizer-weak
    (implies (funname-p x)
             (atom x))
    :rule-classes :compound-recognizer))

(define funname-fix ((x funname-p))
  :parents (funname-p)
  :prepwork ((local (in-theory (enable funname-p))))
  :returns (x-fix funname-p)
  :inline t
  (mbe :logic (if (funname-p x)
                  x
                nil)
       :exec x)
  ///
  (defthm funname-fix-when-funname-p
    (implies (funname-p x)
             (equal (funname-fix x)
                    x))))

(deffixtype funname
  :pred funname-p
  :fix funname-fix
  :equiv funname-equiv
  :forward t
  :define t)

(deflist funnamelist
  :elt-type funname)


(deftypes terms

  (defflexsum term
    :measure (acl2::two-nats-measure (acl2-count x)
                                     (if (consp x)
                                         1
                                       0))
    (:var
     :cond (atom x)
     :fields ((name :acc-body x :type variable))
     :ctor-body name)
    (:const
     :cond (constant-p x)
     :fields ((val :acc-body (constant->val x)))
     :ctor-body (constant x))
    (:fn
     :cond (and (consp x)
                (atom (car x)))
     :fields ((fn   :acc-body (car x) :type funname-p)
              (args :acc-body (cdr x) :type termlist-p))
     :ctor-body (hons fn args))
    (:lambda
     :shape (and (consp x)
                 (tuplep 3 (car x))
                 (eq (caar x) 'lambda))
     :fields ((formals :acc-body (second (car x))
                       :type variablelist-p)
              (body    :acc-body (third (car x))
                       :type term-p)
              (args    :acc-body (cdr x)
                       :type termlist-p
                       :reqfix (take (len formals) args)))
     :require (eql (len formals) (len args))
     :ctor-body (hons (hons-list 'lambda formals body) args)))

  (deflist termlist
    :measure (acl2::two-nats-measure (acl2-count x) 1)
    :elt-type term
    :elementp-of-nil t
    :true-listp t))

   



(define lambda-p (x)
  :returns bool
  (and (consp x)
       (tuplep 3 (car x))
       (eq (first (car x)) 'lambda)
       (variablelist-p (second (car x)))
       (



;; (defevaluator evl evl-list
;;       ((length x) (member-equal x y)))



(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(defxdoc foo)
(set-default-parents foo)

(fty::deflist natlist
  :elt-type natp)

(xdoc 'foo)
