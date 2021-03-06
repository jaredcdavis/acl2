; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "4vec")
(include-book "svex")
(include-book "std/lists/list-defuns" :dir :system)
(include-book "std/util/defval" :dir :system)
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (in-theory (disable acl2::nth-when-zp)))

(defxdoc evaluation
  :parents (expressions)
  :short "Evaluation semantics of @(see svex) expressions.")

(local (xdoc::set-default-parents evaluation))

(fty::deflist 4veclist
  :elt-type 4vec
  :true-listp t
  :parents (4vec))

(define 4veclist-nth-safe ((n natp) (x 4veclist-p))
  :parents (4veclist)
  :short "Like @(see nth) but, with proper @(see fty-discipline) for @(see
4veclist)s.  ``Safely'' causes a run-time error if @('n') is out of bounds."
  :returns (elt 4vec-p)
  (mbe :logic (4vec-fix (nth n x))
       :exec (or (nth n x)
                 (raise "Index ~x0 too large for 4veclist of length ~x1." n (len x))
                 (4vec-x)))
  ///
  (deffixequiv 4veclist-nth-safe
    :hints(("Goal" :in-theory (enable 4veclist-fix))))

  (defthm 4veclist-nth-safe-of-nil
    (equal (4veclist-nth-safe n nil)
           (4vec-x)))

  (defthm 4veclist-nth-safe-of-cons
    (implies (syntaxp (quotep n))
             (equal (4veclist-nth-safe n (cons a b))
                    (if (zp n)
                        (4vec-fix a)
                      (4veclist-nth-safe (1- n) b))))))


(fty::defalist svex-env
  :key-type svar
  :val-type 4vec
  :true-listp t
  :short "An alist mapping @(see svar)s to @(see 4vec)s.  Often used as an
environment that gives variables their values in @(see svex-eval)."
  ///
  (defthm svex-env-p-of-append
    (implies (and (svex-env-p x)
                  (svex-env-p y))
             (svex-env-p (append x y)))
    :hints(("Goal" :in-theory (enable svex-env-p)))))

(define svex-env-acons ((var svar-p) (val 4vec-p) (env svex-env-p))
  :returns (new-env svex-env-p)
  :parents (svex-env)
  :short "Extend an @(see svex-env) with a new variable binding.  Does not
expect or preserve @(see fast-alists)."
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p))))
  (mbe :logic (cons (cons (svar-fix var)
                          (4vec-fix val))
                    (svex-env-fix env))
       :exec (cons (cons var val) env))
  ///
  (deffixequiv svex-env-acons))

(define svex-env-lookup ((var svar-p) (env svex-env-p))
  :parents (svex-env)
  :short "(Slow) Look up a variable's value in an @(see svex-env)."
  :long "<p>We treat any unbound variables as being bound to infinite Xes.</p>"
  :returns (val 4vec-p)
  :prepwork ((local (defthm assoc-is-hons-assoc-equal-when-svex-env-p
                      (implies (svex-env-p env)
                               (equal (assoc var env)
                                      (hons-assoc-equal var env)))
                      :hints(("Goal" :in-theory (enable svex-env-p))))))
  (mbe :logic
       (4vec-fix (cdr (hons-assoc-equal (svar-fix var) (svex-env-fix env))))
       :exec
       (let ((look (assoc-equal var env)))
         (if look
             (cdr look)
           (4vec-x))))
  ///
  (deffixequiv svex-env-lookup)

  (defthm svex-env-lookup-in-empty
    (equal (svex-env-lookup var nil) (4vec-x)))

  (defthm svex-env-lookup-in-svex-env-acons
    (equal (svex-env-lookup var1 (svex-env-acons var2 val env))
           (if (svar-equiv var1 var2)
               (4vec-fix val)
             (svex-env-lookup var1 env)))
    :hints(("Goal" :in-theory (enable svex-env-acons)))))

(define svex-env-boundp ((var svar-p) (env svex-env-p))
  :parents (svex-env)
  :short "(Slow) Check whether a variable is bound in an @(see svex-env)."
  :returns (boundp)
  :prepwork ((local (defthm assoc-is-hons-assoc-equal-when-svex-env-p
                      (implies (svex-env-p env)
                               (equal (assoc var env)
                                      (hons-assoc-equal var env)))
                      :hints(("Goal" :in-theory (enable svex-env-p))))))
  (mbe :logic (consp (hons-assoc-equal (svar-fix var) (svex-env-fix env)))
       :exec (consp (assoc-equal var env))))

(define svex-env-fastlookup ((var svar-p)
                             (env svex-env-p "Must be a @(see fast-alist)."))
  :parents (svex-env)
  :short "Fast lookup in a fast @(see svex-env)."
  :enabled t
  :guard-hints (("goal" :in-theory (enable svex-env-lookup)))
  (mbe :logic (svex-env-lookup var env)
       :exec (let ((look (hons-get var env)))
               (if look
                   (cdr look)
                 (4vec-x)))))


;; Svex symbol maps to actual function called followed by element types
(defval *svex-op-table*
  :parents (svex-functions)
  :short "Raw table about the known svex functions."
  '((id        4vec-fix            (x)                 "identity function")
    (bitsel    4vec-bit-extract    (index x)           "bit select")
    (unfloat   3vec-fix            (x)                 "change Z bits to Xes")
    (bitnot    4vec-bitnot         (x)                 "bitwise negation")
    (bitand    4vec-bitand         (x y)               "bitwise AND")
    (bitor     4vec-bitor          (x y)               "bitwise OR")
    (bitxor    4vec-bitxor         (x y)               "bitwise XOR")
    (res       4vec-res            (x y)               "resolve (short together)")
    (resand    4vec-resand         (x y)               "resolve wired AND")
    (resor     4vec-resor          (x y)               "resolve wired OR")
    (override  4vec-override       (x y)               "resolve different strengths")
    (onp       4vec-onset          (x)                 "identity, except Z becomes 0")
    (offp      4vec-offset         (x)                 "negation, except Z becomes 0")
    (uand      4vec-reduction-and  (x)                 "unary (reduction) AND")
    (uor       4vec-reduction-or   (x)                 "unary (reduction) OR")
    (uxor      4vec-parity         (x)                 "reduction XOR, i.e. parity")
    (zerox     4vec-zero-ext       (width x)           "zero extend")
    (signx     4vec-sign-ext       (width x)           "sign extend")
    (concat    4vec-concat         (width x y)         "concatenate at a given bit width")
    (blkrev    4vec-rev-blocks     (width bsz x)       "reverse order of blocks")
    (rsh       4vec-rsh            (shift x)           "right shift")
    (lsh       4vec-lsh            (shift x)           "left shift")
    (+         4vec-plus           (x y)               "addition")
    (b-        4vec-minus          (x y)               "subtraction")
    (u-        4vec-uminus         (x)                 "unary minus")
    (*         4vec-times          (x y)               "multiplication")
    (/         4vec-quotient       (x y)               "division")
    (%         4vec-remainder      (x y)               "modulus")
    (xdet      4vec-xdet           (x)                 "identity on binary vectors, else X")
    (<         4vec-<              (x y)               "less than")
    (==        4vec-==             (x y)               "equality")
    (===       4vec-===            (x y)               "case equality")
    (==?       4vec-wildeq         (x y)               "wildcard equality")
    (==??      4vec-symwildeq      (x y)               "wildcard equality")
    (clog2     4vec-clog2          (x)                 "ceiling of log2")
    (?         4vec-?              (test then else)    "if-then-else")
    (bit?      4vec-bit?           (test then else)    "bitwise if-then-else")))

(encapsulate
  ()
  (local (defun syms->strings (x)
           (if (atom (cdr x))
               (list (symbol-name (car x)))
             (cons (symbol-name (car x))
                   (cons " "
                         (syms->strings (cdr x)))))))

  (local (defun optable-to-xdoc-aux (optable acc)
           ;; collects a reversed list of strings
           (b* (((when (atom optable)) acc)
                ((list name fn args descrip) (car optable))
                (entry `("<tr><td>@('("
                         ,@(syms->strings (cons name args))
                         ")')</td><td>@(see " ,(symbol-name fn)
                         ")</td><td>" ,descrip "</td></tr>" "
")))
             (optable-to-xdoc-aux (cdr optable) (revappend entry acc)))))

  (local (defun optable-to-xdoc ()
           (declare (xargs :mode :program))
           (str::fast-string-append-lst
            `("<p>SVEX has a fixed language of known functions.
The following table shows the function symbols (all in the
SV package) and their meanings.</p>
<table>
<tr><th>SVEX form</th><th>4vec function</th><th>Description</th></tr>
"
              ,@(reverse (optable-to-xdoc-aux *svex-op-table* nil))
              "</table>"))))

  (make-event
   `(defxdoc svex-functions
      :parents (expressions)
      :short "The known svex functions symbols and their meanings."
      :long ,(optable-to-xdoc))))


(defsection svex-apply-cases
  :parents (svex-apply)
  :short "Generates the main case statement for @(see svex-apply)."
  :long "@(def svex-apply-cases)"

  (defun svex-apply-collect-args (n max argsvar)
    (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
    (let* ((n   (nfix n))
           (max (nfix max)))
      (if (zp (- max n))
          nil
        (cons `(4veclist-nth-safe ,n ,argsvar)
              (svex-apply-collect-args (+ 1 n) max argsvar)))))

  (defun svex-apply-cases-fn (argsvar optable)
    (b* (((when (atom optable))
          ;; Not a recognized function -- result is all Xes.
          '((otherwise
             (or (raise "Attempting to apply unknown function ~x0~%" fn)
                 (4vec-x)))))
         ((list sym fn args) (car optable))
         (call `(mbe :logic
                     (,fn . ,(svex-apply-collect-args 0 (len args) argsvar))
                     :exec
                     (let ((arity-check (or (eql (len args) ,(len args))
                                            (raise "Improper arity for ~x0: expected ~x1 arguments but found ~x2.~%"
                                                   ',sym ',(len args) (len args)))))
                       (declare (ignore arity-check))
                       (,fn . ,(svex-apply-collect-args 0 (len args) argsvar))))))
      (cons `(,sym ,call)
            (svex-apply-cases-fn argsvar (cdr optable)))))

  (defmacro svex-apply-cases (fn args)
    `(case ,fn
       . ,(svex-apply-cases-fn args *svex-op-table*))))


(define svex-apply
  :short "Apply an @(see svex) function to some @(see 4vec) arguments."
  ((fn   fnsym-p    "Name of the function to apply.")
   (args 4veclist-p "Arguments to apply it to."))
  :returns (result 4vec-p "Result of applying the function.")
  :long "<p>This function captures function application for @(see svex-eval),
using a big case statement on the @('fn') to execute.</p>

<p>SVEX uses a fixed language of known functions with fixed arities; see @(see
svex-functions) for the list of known functions and their meanings.  If we are
given a known function of proper arity, we execute the corresponding 4vec
operation on its arguments.</p>

<ul>

<li>Attempting to apply any unknown function produces an all-X result in the
logic, and causes a run-time error during execution.</li>

<li>Applying a function to the wrong number of arguments produces an all-X
result in the logic, and causes a run-time error during execution.</li>

</ul>"

  (let* ((fn (mbe :logic (fnsym-fix fn) :exec fn))
         (args (mbe :logic (4veclist-fix args) :exec args)))
    (svex-apply-cases fn args))
  ///
  (deffixequiv svex-apply)

  ;; Quick checks that arity checking and invalid function checking is working.
  ;; BOZO it would be nice to do these with must-fail, but that doesn't seem
  ;; to work.

  ;; (svex-apply 'bad-function nil)
  ;; (svex-apply 'id (list (4vec-x) (4vec-x)))
  ;; (svex-apply 'id nil)
  )


(defines svex-eval
  :parents (evaluation)
  :short "Evaluate an @(see svex) in some environment."

  :long "<p>@('svex-eval') is a straightforward evaluator for @(see svex)
formulas.  It takes as arguments an @(see svex) object to evaluate, and an
environment mapping variables (@(see svar) objects) to @(see 4vec) values.  It
returns the @(see 4vec) value of the formula, under this assignment, in the
obvious way:</p>

<ul>

<li>Constants evaluate to themselves.</li>

<li>Variables are looked up using @(see svex-env-fastlookup).  Note that any
unbound variables evaluate to an infinite-width X.</li>

<li>Functions applications are handled with @(see svex-apply).</li>

</ul>

<p>We typically expect @(see svex)es to be constructed with @(see hons).  To
take advantage of this structure sharing, we @(see memoize) @(see
svex-eval).</p>"

  :flag svex-eval-flag
  :flag-local nil
  :verify-guards nil

  (define svex-eval ((x   svex-p     "Expression to evaluate.")
                     (env svex-env-p "Variable bindings.  Must be a @(see fast-alist)."))
    :measure (svex-count x)
    :flag expr
    :returns (val 4vec-p "Value of @('x') under this environment."
                  :hints ((and stable-under-simplificationp
                               '(:expand ((4vec-p x))))))
    (svex-case x
      :quote x.val
      :var   (svex-env-fastlookup x.name env)
      :call  (svex-apply x.fn (svexlist-eval x.args env))))

  (define svexlist-eval
    :parents (evaluation)
    :short "Evaluate each @(see svex) in a list under the same environment."
    ((x   svexlist-p "List of expressions to evaluate.")
     (env svex-env-p "Variable bindings.  Must be a @(see fast-alist)."))
    :returns (vals 4veclist-p "Values of the expressions in @('x') under this environment.")
    :measure (svexlist-count x)
    :flag list

    (if (atom x)
        nil
      (cons (svex-eval (car x) env)
            (svexlist-eval (cdr x) env))))
  ///

  (verify-guards svex-eval)
  (memoize 'svex-eval :condition '(eq (svex-kind x) :call)))

(defsection svexlist-eval-basics
  :parents (svexlist-eval)
  :short "Very basic list lemmas for @(see svexlist-eval)."

  (local (in-theory (enable svex-eval
                            svexlist-eval)))

  (defthm svexlist-eval-nil
    (equal (svexlist-eval nil env)
           nil))

  (defthm car-of-svexlist-eval
    (4vec-equiv (car (svexlist-eval x env))
                (svex-eval (car x) env)))

  (defthm cdr-of-svexlist-eval
    (4veclist-equiv (cdr (svexlist-eval x env))
                    (svexlist-eval (cdr x) env)))

  (defthm svexlist-eval-of-cons
    (equal (svexlist-eval (cons a b) env)
           (cons (svex-eval a env)
                 (svexlist-eval b env))))

  (defthm len-of-svexlist-eval
    (equal (len (svexlist-eval x env))
           (len x)))

  (defthm svexlist-eval-of-append
    (equal (svexlist-eval (append a b) env)
           (append (svexlist-eval a env)
                   (svexlist-eval b env)))))

(defsection svex-eval-basics
  :parents (svex-eval)
  :short "Very basic lemmas about @(see svex-eval)."

  (local (in-theory (enable svex-eval
                            svexlist-eval)))

  "<h3>Congruence rules</h3>"

  (deffixequiv-mutual svex-eval
    :hints (("goal" :expand ((svexlist-fix x)))))

  "<h3>Svex-eval of constants/constructors</h3>"

  (make-event
   `(encapsulate nil
      (set-ignore-ok t)
      (defthm svex-eval-of-quoted
        (implies (syntaxp (quotep x))
                 (equal (svex-eval x env)
                        ,(acl2::body 'svex-eval nil (w state))))
        :hints(("Goal" :in-theory (enable svex-eval))))))

  (defthm svex-eval-of-svex-call
    (equal (svex-eval (svex-call fn args) env)
           (svex-apply fn (svexlist-eval args env)))
    :hints(("Goal" :expand ((svex-eval (svex-call fn args) env)))))

  (defthm svex-eval-when-fncall
    (implies (equal (svex-kind x) :call)
             (equal (svex-eval x env)
                    (svex-apply (svex-call->fn x)
                                (svexlist-eval (svex-call->args x) env))))
    :hints(("Goal" :in-theory (enable svex-eval))))

  (defthm svex-eval-when-quote
    (implies (eq (svex-kind x) :quote)
             (equal (svex-eval x env)
                    (svex-quote->val x)))
    :hints(("Goal" :in-theory (enable svex-eval)))))



(define svex-alist-eval-aux ((x   svex-alist-p)
                             (env svex-env-p))
  :parents (svex-alist-eval)
  :prepwork ((local (in-theory (enable svex-alist-p svex-alist-fix svex-env-p))))
  :returns (xx svex-env-p :hints(("Goal" :in-theory (enable svex-env-p))))
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (cons (mbe :logic (svar-fix (caar x))
                         :exec (caar x))
                    (svex-eval (cdar x) env))
              (svex-alist-eval-aux (cdr x) env))
      (svex-alist-eval-aux (cdr x) env))))

(define svex-alist-eval
  :parents (evaluation svex-alist)
  :short "Evaluate every expression in an @(see svex-alist) under the same environment."
  ((x   svex-alist-p "Alist of variables to @(see svex) expressions to evaluate.
                      Need not be fast.")
   (env svex-env-p   "Environment to evaluate the expressions under.  Should
                      be a @(see fast-alist)."))
  :prepwork ((local (in-theory (enable svex-alist-p svex-alist-fix svex-env-p))))
  :returns (result svex-env-p
                   "New (slow) alist, binds the variables to their expressions'
                    values."
                   :hints(("Goal" :in-theory (enable svex-env-p))))
  :Verify-guards nil
  (mbe :logic
       (if (atom x)
           nil
         (if (mbt (consp (car x)))
             (cons (cons (mbe :logic (svar-fix (caar x))
                              :exec (caar x))
                         (svex-eval (cdar x) env))
                   (svex-alist-eval (cdr x) env))
           (svex-alist-eval (cdr x) env)))
       :exec (with-fast-alist env (svex-alist-eval-aux x env)))
  ///
  (deffixequiv svex-alist-eval)

  (local (defthm svex-alist-eval-aux-elim
           (equal (svex-alist-eval-aux x env)
                  (svex-alist-eval x env))
           :hints(("Goal" :in-theory (enable svex-alist-eval-aux)))))

  (verify-guards svex-alist-eval)

  (defthm svex-env-lookup-of-svex-alist-eval
    (equal (svex-env-lookup k (svex-alist-eval x env))
           (let ((xk (svex-lookup k x)))
             (if xk (svex-eval xk env) (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup svex-lookup))))

  (defthm svex-alist-eval-of-append
    (equal (svex-alist-eval (append a b) env)
           (append (svex-alist-eval a env)
                   (svex-alist-eval b env)))
    :hints(("Goal" :in-theory (enable svex-alist-eval append)))))





(defalist svar-boolmasks
  :key-type svar
  :val-type integerp)

(define svar-boolmasks-lookup ((v svar-p) (boolmasks svar-boolmasks-p))
  :returns (boolmask integerp :rule-classes :type-prescription)
  (ifix (cdr (hons-get (mbe :logic (svar-fix v) :exec v)
                       (svar-boolmasks-fix boolmasks))))
  ///
  (deffixequiv svar-boolmasks-lookup))



;; Placeholder: this is used by svtvs, b/c it is advantageous in symbolic
;; evaluation to hold constant a set of variables that are expected to possibly
;; be bound in the environment.  Logically, these are irrelevant.
(define svexlist-eval-with-vars ((x svexlist-p)
                                 (vars svarlist-p)
                                 (boolmasks svar-boolmasks-p)
                                 (env svex-env-p))
  :ignore-ok t
  :enabled t
  (svexlist-eval x env))

(define svex-alist-eval-with-vars ((x svex-alist-p)
                                   (vars svarlist-p)
                                   (boolmasks svar-boolmasks-p)
                                   (env svex-env-p))
  :returns (res (equal res (svex-alist-eval x env))
                :hints(("Goal" :in-theory (enable svex-alist-eval pairlis$ svex-alist-keys
                                                  svex-alist-vals svexlist-eval))))
  (pairlis$ (svex-alist-keys x)
            (svexlist-eval-with-vars (hons-copy (svex-alist-vals x)) vars boolmasks env)))









(defsection svcall
  :parents (svex)
  :short "Safely construct an @(see svex) for a function call."

  :long "<p>@('(call svcall)') just constructs an @(see svex) that applies
@('fn') to the given @('args').  This macro is ``safe'' in that, at compile
time, it ensures that @('fn') is one of the known functions (see the @(see
svex-functions)) and that it is being given the right number of arguments.</p>

@(def svcall)"

  (defun svcall-fn (fn args)
    (declare (xargs :guard t))
    (b* ((look (assoc fn *svex-op-table*))
         ((unless look)
          (er hard? 'svcall "Svex function doesn't exist: ~x0" fn))
         (formals (third look))
         ((unless (eql (len formals) (len args)))
          (er hard? 'svcall "Wrong arity for call of ~x0" fn)))
      `(svex-call ',fn (list . ,args))))

  (defmacro svcall (fn &rest args)
    (svcall-fn fn args)))
