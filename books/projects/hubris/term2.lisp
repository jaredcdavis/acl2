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

(define hons-member-equal (a x)
  :enabled t
  (mbe :logic (member-equal a x)
       :exec
       (cond ((atom x)
              nil)
             ((hons-equal a (car x))
              x)
             (t
              (hons-member-equal a (cdr x))))))


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


(define funname-p (x)
  :returns bool
  (and (symbolp x)
       x
       (not (eq x 'quote)))
  ///
  (defthm funname-not-quote
    (implies (funname-p x)
             (not (equal x 'quote)))
    :rule-classes :forward-chaining)

  (defthm funname-compound-recognizer
    (implies (funname-p x)
             (and (symbolp x) x))
    :rule-classes :compound-recognizer))

(define funname-fix ((x funname-p))
  :returns (name funname-p)
  :prepwork ((local (in-theory (enable funname-p))))
  :inline t
  (mbe :logic (if (funname-p x)
                  x
                'equal)
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
  :define t
  :forward t)

(deftypes term

  (defflexsum term
    (:var
     :cond (atom x)
     :fields ((name :acc-body x :type variable-p))
     :ctor-body name
     :ctor-name var
     :type-name var
     :inline (:xtor :acc))

    (:const
     :cond (eq (car x) 'quote)
     :shape (and (consp (cdr x))
                 (not (cddr x)))
     :fields ((val :acc-body (cadr x)))
     :ctor-body (hons-list 'quote val)
     :ctor-name const
     :type-name const)

    (:call
     :fields ((fn   :acc-body (car x) :type fun-p)
              (args :acc-body (cdr x) :type termlist-p))
     :ctor-body (hons fn args)
     :ctor-name call
     :type-name call
     :inline (:xtor :acc)))

  (defflexsum fun
    (:fn
     :cond (atom x)
     :fields ((name :acc-body x :type funname-p))
     :ctor-body name
     :ctor-name fn
     :type-name fn
     :inline (:xtor :acc))

    (:lambda
     :shape (and (eq (car x) 'lambda)
                 (consp (cdr x))
                 (consp (cddr x))
                 (not (cdddr x)))
     :fields ((formals :acc-body (cadr x)  :type variablelist-p)
              (body    :acc-body (caddr x) :type term-p))
     :ctor-body (hons-list 'lambda formals body)
     :ctor-name lam
     :type-name lam))

  (deflist termlist :elt-type term-p))





; So that seems like a nice-ish, fty-style term representation.

; A question, though, is how to make ANY new term representation directly
; usable by ACL2.  Let's try to write a clause processor that works with these
; terms.


(defsection clause-p
  :short "A clause is just a list of terms."

  (defmacro clause-p (x)
    `(termlist-p ,x)))


; Our clause processor will just prove trivial clauses with negated terms.

(define match-call-of ((name funname-p)
                       (term term-p))
  :returns (bool booleanp)
  (term-case term
    (:call (fun-case term.fn
             (:fn (equal (funname-fix name) term.fn.name))
             (otherwise nil)))
    (otherwise nil))
  ///
  (defthm term-kind-when-match-call-of
    (implies (match-call-of name term)
             (equal (term-kind term) :call))))



(define dumb-negate ((x term-p))
  :returns (not-x term-p)
  (if (and (match-call-of 'not x)
           (consp (call->args x)))
      (first (call->args x))
    (make-call :fn (make-fn :name 'not)
               :args (hons-list x))))


(define dumb-clause-true-p ((x termlist-p))
  (cond ((atom x)
         nil)
        ((hons-member-equal (dumb-negate (car x))
                            (termlist-fix (cdr x)))
         t)
        (t
         (dumb-clause-true-p (cdr x)))))




(defevaluator ev evlst
  ((not x)
   (if x y z)
   (equal x y)))





(define my-cp (clause)

;; so probably we'd need some automatic way to "promote" the evaluator into an
;; evaluator about our new kind of terms, and a mapping for converting
;; pseudo-termp's into our nice terms, and back from our nice terms.  We could
;; really simplify this conversion stuff by making pseudo-termp structurally
;; equal to our term structures.  BUT, that's not really what we want to do
;; anyway, because the stupid evaluators won't satisfy nice term congruences
;; anyway.  The problem is the damn (and x (cdr (assoc-equal ...))) case in the
;; evaluator.  So how can we get a congruence for an evaluator?


; OK, BUT!!!!!

;; Maybe we don't even give a shit about evaluators because we can develop our
;; own proof format and argue things that way.





  clause)



(defthm my-cp-correct
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (ev (acl2::conjoin-clauses (my-cp cl)) a))
           (ev (acl2::disjoin cl) a))
  :rule-classes :clause-processor)






