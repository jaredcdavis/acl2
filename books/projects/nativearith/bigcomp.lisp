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
(include-book "bigbound")
(include-book "smalleval")
(local (include-book "arith"))
(local (include-book "ceiling"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/alists/hons-assoc-equal" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "tools/do-not" :dir :system))
(local (acl2::do-not generalize fertilize))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable signed-byte-p unsigned-byte-p)))
(local (in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                       (acl2::alist-keys-member-hons-assoc-equal))))

(defsection bigcompile
  :short "Compiler from @(see bigexpr)s into @(see smallexpr)s."
  :long "<h3>Introduction</h3>

<p>We now develop and verify a compiler that can ``statically'' convert @(see
bigexpr)s into equivalent @(see smallexpr)s, when given constraints about the
inputs and outputs of these expressions.</p>

<p>At a high level, the compiler takes as input:</p>

<ul>
<li>The @(see bigexpr)s to be compiled.</li>
<li>Size bounds for the inputs to the expression.</li>
</ul>

<p>It then produces:</p>

<ul>
<li>The compiled, corresponding @(see smallexpr)s.</li>
<li>An input mapping binding @(see bigvar)s to lists of @(see smallvars) that
represent their contents.</li>
</ul>

<p>The correctness statement for the compiler is roughly that the following two
computations are equal:</p>

<ol>

<li>Evaluate the bigexpr in a @(see bigenv) that binds each variable to a value
of the appropriate size.</li>

<li>Translate the environment into a corresponding @(see smallenv) using the
generated input mapping.  Then, evaluate the smallexprs in this smallenv.
Finally, coerce the resulting values as a bignum.</li>

</ol>

<p>Why do we need size bounds for the inputs?  Our compiler is intended to
convert bigexprs into smallexprs in an entirely static way.  That is, the
resulting smallexprs are data independent, require no dynamic memory
allocation, etc.  To accomplish this, we need to be able to determine an upper
bound on the size of every subexpression.  An immediate consequence is that we
need to know the maximum sizes of the variables that are used in an expression.
For instance, consider an expression like @($a < b$).  If we don't know a bound
on the sizes of @($a$) and @($b$), then we won't be able to bound how many
small operations we need to carry out this comparison.</p>

<p>The compiler uses the width bounds on inputs (and knowledge about the
operators) to infer bounds for subexpressions.  We don't bother with size
bounds for the outputs, because we figure that if you can wrap your expressions
in @(see bignum-loghead) or @(see bignum-logext) calls if you only care about
getting N bits out.</p>")

(local (xdoc::set-default-parents bigcompile))

; Design decision: no care masks (at least, not yet).
;
; Perhaps the compiler should know about care masks.  For instance, doing so
; much allow us to avoid constructing a lot of small expressions, e.g., if we
; are compiling (logbit 4 (logand a b)), then even if A and B are 1000 bit
; numbers, we might be smart enough to only do the AND on their least
; significant blocks.
;
; On the other hand, adding care masks would complicate the compiler and we
; could certainly do this kind of optimization later, as a rewriter on small
; expressions.  So I think, for now, to keep things simple, let's not try to
; use care masks in the compiler itself.



; Compiling Constants ---------------------------------------------------------
;
; This much is easy, at least. :)

(define smallvals->bigint ((x i64list-p))
  :guard (consp x)
  :returns (big bigint-p)
  (cond ((atom x)
         (bigint-0))
        ((atom (cdr x))
         (bigint-singleton (car x)))
        (t
         (bigint-cons (car x) (smallvals->bigint (cdr x)))))
  ///
  (defrule smallvals->bigint-when-atom
    (implies (atom x)
             (equal (smallvals->bigint x) (bigint-0))))
  (defrule smallvals->bigint-of-cons
    (equal (smallvals->bigint (cons a x))
           (if (consp x)
               (bigint-cons a (smallvals->bigint x))
             (bigint-singleton a)))))

(define bigint-const-compile ((x bigint-p))
  :returns (smallexprs (and (smallexprlist-p smallexprs)
                            (consp smallexprs)))
  :short "Compile a single, constant @(see bigint) into a list of (constant)
          @(see smallexpr)s."
  :measure (bigint-count x)
  (b* (((bigint x))
       ((when x.endp)
        (list (make-smallexpr-const :val x.first))))
    (cons (make-smallexpr-const :val x.first)
          (bigint-const-compile x.rest)))
  ///
  (defrule bigint-const-compile-correct
    (let* ((smallexprs (bigint-const-compile x))
           (smallvals  (smalleval-list smallexprs env)))
      (equal (bigint->val (smallvals->bigint smallvals))
             (bigint->val x)))))


; Compiling Variables ---------------------------------------------------------
;
; Variables are much trickier than constants because we need to introduce new
; variables to hold each chunk of the corresponding bigvar.
;
; One approach (but not the approach we will follow) would be to base our work
; on some kind of explicit mapping of bigvars to smallvars.  We would have:
;
;    (1) A representation for a map from bigvar to smallvarlist, which could
;        probably just be a fast alist or similar.
;
;    (2) A function for looking up the small variables for a bigvar in such a
;        map.  The compiler would use this function when translating bigvars.
;
;    (3) A function to translate a bigenv into a smallenv: it would need to map
;        each (bigvar . bigint) binding into a list of (smallvar . i64)
;        bindings for each chunk.
;
;    (4) A predicate to ensure that the map is sensible: it would need to give
;        us enough smallvars for each bigvar (per the bigvarsizes), and do some
;        kind of minimal uniqueness checking to ensure that there aren't
;        clashes when we translate different bigvars.
;
;    (5) A function for constructing a sensible map.
;
;    (6) Proof work to show how all of these things work together.
;
; Though tedious, this would probably all be fairly straightforward.  But to
; try to avoid some of this work, below we instead try to avoid having an
; explicit mapping from bigvars to smallvarlists by using subscripts to
; implicitly map each bigvar V to smallvars (V_1 V_2 ... V_n), where N is
; derived from the variable's size and each smallvar is formed by adding an
; appropriate subscript to the bigvar's name.
;
; This avoiding needing an explicit mapping as in (1) and uniqueness and size
; adequacy checks as in (4).  We essentially fold the map construction (5) into
; the variable lookup function (2).  This incidentally simplifies (3), insofar
; as that it no longer needs an explicit mapping.  We still end up needing some
; proof work to show that our maps are sufficiently unique.  But we would have
; needed that anyway.

(defprojection smallvarlist->names ((x smallvarlist-p))
  :parents (smallvarlist)
  (smallvar->name x))


(define make-related-smallvars (base-name (n natp))
  :returns (vars smallvarlist-p)
  :parents (explode-bigvar-to-smallvars)
  :short "Create @('n') distinct @(see smallvar)s that share some base name.
  Typically these will represent successive chunks of a @(see bigint)."
  (b* (((when (zp n))
        nil)
       (n (- n 1))
       (var1 (make-smallvar :name base-name
                            :subscripts (list n))))
    (cons var1 (make-related-smallvars base-name n)))
  ///
  (defthm consp-of-make-related-smallvars
    (equal (consp (make-related-smallvars base-name n))
           (posp n)))

  (defthm make-related-smallvars-under-iff
    (iff (make-related-smallvars base-name n)
         (posp n)))

  (defrule len-of-make-related-smallvars
    (equal (len (make-related-smallvars base-name n))
           (nfix n)))

  (defrule smallvar->name-when-member-of-make-related-smallvars
    (implies (member a (make-related-smallvars base-name n))
             (equal (smallvar->name a)
                    base-name)))

  (defrule smallvarlist->names-of-make-related-smallvars
    (equal (smallvarlist->names (make-related-smallvars base-name n))
           (repeat (nfix n) base-name))
    :hints(("Goal" :in-theory (enable repeat))))

  (local (defrule l0
           (implies (equal free (list x))
                    (equal (len free) 1))))

  (local (defrule l1
           (implies (equal free (list x))
                    (equal (car free) x))))

  (local (defrule l2
           (implies (member a (make-related-smallvars base-name n))
                    (and (equal (len (smallvar->subscripts a)) 1)
                         (<= 0 (car (smallvar->subscripts a)))
                         (< (car (smallvar->subscripts a)) (nfix n))))
           :enable len))

  (local (defrule l3
           (implies (<= (nfix n) (car (smallvar->subscripts a)))
                    (not (member a (make-related-smallvars base-name n))))))

  (defrule no-duplicatesp-equal-of-make-related-smallvars
    (no-duplicatesp-equal (make-related-smallvars base-name n))))


(define explode-bigvar-to-smallvars ((var      bigvar-p)
                                     (varsizes bigvarsizes-p))
  :returns (vars smallvarlist-p)
  :parents (explode-bigenv)
  :short "Create @(see smallvar)s for the chunks of some @(see bigvar)."
  (let* ((var          (bigvar-fix var))
         (size-in-bits (bigvarsize-lookup var varsizes))
         (size-in-i64s (ceiling size-in-bits 64)))
    (make-related-smallvars var size-in-i64s))
  ///
  (defrule len-of-explode-bigvar-to-smallvars
    (equal (len (explode-bigvar-to-smallvars var varsizes))
           (ceiling (bigvarsize-lookup var varsizes) 64)))

  (defrule consp-of-explode-bigvar-to-smallvars
    (and (consp (explode-bigvar-to-smallvars var varsizes))
         (true-listp (explode-bigvar-to-smallvars var varsizes)))
    :rule-classes :type-prescription)

  (defrule smallvar->name-when-member-of-explode-bigvar-to-smallvars
    (implies (member a (explode-bigvar-to-smallvars var varsizes))
             (equal (smallvar->name a)
                    (bigvar-fix var))))

  (defrule smallvarlist->names-of-explode-bigvar-to-smallvars
    (equal (smallvarlist->names (explode-bigvar-to-smallvars var varsizes))
           (repeat (ceiling (bigvarsize-lookup var varsizes) 64)
                   (bigvar-fix var)))
    :hints(("Goal" :in-theory (enable repeat))))

  (defrule no-duplicatesp-equal-of-explode-bigvar-to-smallvars
    (no-duplicatesp-equal (explode-bigvar-to-smallvars var varsizes)))

  (memoize 'explode-bigvar-to-smallvars))


(define explode-bigint-to-len ((len natp)
                               (big bigint-p))
  :returns (chunks i64list-p)
  :parents (explode-bigenv)
  :short "Break a @(see bigint) into some given number of chunks."
  (b* (((when (zp len))
        nil)
       ((bigint big)))
    (cons big.first
          (explode-bigint-to-len (- len 1) big.rest)))
  ///
  (defrule len-of-explode-bigint-to-len
    (equal (len (explode-bigint-to-len len big))
           (nfix len)))

  (local (defrule a0
           (equal (- (- x)) (fix x))))

  (local (defrule a1
           (equal (* -1 n) (- n))))

  (local (defrule l1
           (implies (and (posp n)
                         (posp size))
                    (equal (logext (* n size) (logapp n head tail))
                           (if (equal size 1)
                               (logext n head)
                             (logapp n head (logext (* n (+ -1 size)) tail)))))
           :nonlinearp t
           :disable (logext-of-logapp-less)
           :use ((:instance logext-of-logapp-less
                  (n (* n size))
                  (m n)
                  (a head)
                  (b tail)))))

  (local (defrule l2
           (iff (consp (explode-bigint-to-len len big))
                (posp len))))

  (defrule explode-bigint-to-len-correct
    (implies (posp len)
             (equal (bigint->val (smallvals->bigint (explode-bigint-to-len len big)))
                    (logext (* len 64) (bigint->val big))))
    :expand ((bigint->val big))))


(define explode-bigenv-entry ((var bigvar-p)
                              (val bigint-p)
                              (varsizes bigvarsizes-p))
  :parents (explode-bigenv)
  :returns (env smallenv-p)
  :short "Translate a single @('(bigvar . bigint)') pair into corresponding
  @('(smallvar . smallint)') pairs, one for each chunk."
  (b* ((smallvars (explode-bigvar-to-smallvars var varsizes))
       (smallvals (explode-bigint-to-len (len smallvars) val)))
    (pairlis$ smallvars smallvals))
  :prepwork
  ((local (defrule smallenv-p-of-pairlis$
            (implies (and (smallvarlist-p vars)
                          (i64list-p vals)
                          (equal (len vars) (len vals)))
                     (smallenv-p (pairlis$ vars vals))))))
  ///
  (defrule alist-keys-of-explode-bigenv-entry
    (equal (alist-keys (explode-bigenv-entry var val varsizes))
           (explode-bigvar-to-smallvars var varsizes))))


(define explode-bigenv ((bigenv   bigenv-p)
                        (varsizes bigvarsizes-p))
  :returns (smallenv smallenv-p)
  :short "Translate a @(see bigenv) into a corresponding @(see smallenv)."
  :long "<p>A @(see bigvarsizes) mapping gives us size bounds for all of the
  variables we might encounter in a @(see bigenv).  Using this mapping, we can
  figure out how many small variables we need to represent each bigvar, and
  then just translate each @('(bigvar . bigint)') pair in the @(see bigenv)
  into a list of corresponding @('(smallvar . smallint)') pairs, one for each
  chunk.  The result is a @(see smallenv) that ``emulates'' the original @(see
  bigenv).</p>"
  :measure (bigenv-count bigenv)
  (b* ((bigenv (bigenv-fix bigenv))
       ((when (atom bigenv))
        nil)
       ((cons var val) (car bigenv)))
    (append (explode-bigenv-entry var val varsizes)
            (explode-bigenv (cdr bigenv) varsizes)))

  ///

  (local (in-theory (enable explode-bigenv)))

; Roughly the correctness claim is: If we evaluate the smallvars (V1 ... Vn)
; for any bigvar V in the exploded environment, we get the same thing as just
; evaluating V in the original environment.  The proof is by induction on
; explode-bigenv.  It is completely straightforward except that we have to know
; a lot about the uniqueness of the variables we're generating.
;
; Base Step.  When we are at the end of the bigenv, i.e., Bigenv is NIL and the
; exploded environment is also NIL.  Here, evaluating V always gives 0, but so
; does evaluating Vi for any Vi, so this all works out.
;
; Inductive Step.  When we are NOT at the end of the bigenv.  Then consider two
; cases: (1) V is the first variable in the environment, or (2) it is some
; other variable.
;
; Case 1. The bigenv is ((V . VAL) ...), so evaluating V in it yields VAL.
; Meanwhile the exploded smallenv is:
;
;    (append ((V1 . VAL[63:0]) ... (VN . VAL[...]))  // exploded (V . VAL) pair
;            rest-of-smallenv)                       // exploded remainder of bigenv
;
; So, because of name uniqueness, evaluating (V1 ... Vn) in this smallenv will
; give us exactly the chunks of VAL.
;
; Case 2. The bigenv starts with some variable other than V, call it W.  Then
; the exploded smallenv is
;
;    (append ((W1 . WVal[63:0]) ... (Wn . WVal[...]))  // exploded (W . WVal)
;            rest-of-smallenv)                         // exploded remainder of bigenv
;
; Because of name uniqueness, evaluating (V1 ... Vn) in this smallenv is just
; the same as evaluating (V1 ... Vn) in rest-of-smallenv.  Then we can appeal
; to induction and we are done.

; *** Base Step ***

  (local (defrule bigenv-lookup-when-atom
           (implies (atom (bigenv-fix env))
                    (equal (bigenv-lookup var env)
                           (bigint-0)))
           :enable (bigenv-lookup bigenv-fix)))

  (local (defrule smalleval-lookup-of-var-in-nil
           (equal (smallenv-lookup name nil)
                  0)
           :hints(("Goal" :in-theory (enable smallenv-lookup)))))

  (local (defrule smalleval-of-var-in-nil
           (implies (smallexpr-case x :var)
                    (equal (smalleval x nil)
                           0))
           :expand ((smalleval x nil))))

  (local (defrule smalleval-list-of-smallexprs-from-smallvars
           (equal (smalleval-list (smallexprs-from-smallvars x) nil)
                  (repeat (len x) 0))
           :enable (repeat)))

  (local (defthm smallvals->bigint-of-repeat-0
           (equal (bigint->val (smallvals->bigint (repeat n 0)))
                  0)
           :hints(("Goal" :in-theory (enable smallvals->bigint repeat)))))


; *** Induction Case ***

  (local (defrule smallenv-lookup-of-append
           (equal (smallenv-lookup var (append env1 env2))
                  (if (member (smallvar-fix var) (alist-keys (smallenv-fix env1)))
                      (smallenv-lookup var env1)
                    (smallenv-lookup var env2)))
           :enable (smallenv-lookup)))

  (local (defrule smalleval-var-of-append
           (implies (smallexpr-case x :var)
                    (equal (smalleval x (append env1 env2))
                           (if (member (smallexpr-var->var x) (alist-keys (smallenv-fix env1)))
                               (smalleval x env1)
                             (smalleval x env2))))
           :enable (smalleval)
           :expand ((smalleval x (append env1 env2))
                    (smalleval x env1))))

  (local (defrule case1-cancel-env
           (implies (subsetp-equal (smallvarlist-fix vars) (alist-keys (smallenv-fix env1)))
                    (equal (smalleval-list (smallexprs-from-smallvars vars) (append env1 env2))
                           (smalleval-list (smallexprs-from-smallvars vars) env1)))
           :induct (len vars)))

  (local (defrule case2-cancel-env
           (implies (not (intersectp-equal (smallvarlist-fix vars) (alist-keys (smallenv-fix env1))))
                    (equal (smalleval-list (smallexprs-from-smallvars vars) (append env1 env2))
                           (smalleval-list (smallexprs-from-smallvars vars) env2)))
           :induct (len vars)
           :enable (intersectp-equal)))

  (local
   (defsection case2-crux
     (local (defrule c0
              (implies (and (member a (explode-bigvar-to-smallvars var varsizes))
                            (member a (explode-bigvar-to-smallvars other varsizes)))
                       (equal (bigvar-equiv var other)
                              t))
              :disable (smallvar->name-when-member-of-explode-bigvar-to-smallvars)
              :use ((:instance smallvar->name-when-member-of-explode-bigvar-to-smallvars
                     (a a) (var var) (varsizes varsizes))
                    (:instance smallvar->name-when-member-of-explode-bigvar-to-smallvars
                     (a a) (var other) (varsizes varsizes)))))

     (local (defrule c1
              (implies (and (member a (explode-bigvar-to-smallvars var varsizes))
                            (not (member a (explode-bigvar-to-smallvars other varsizes))))
                       (not (bigvar-equiv var other)))
              :disable (smallvar->name-when-member-of-explode-bigvar-to-smallvars)
              :use ((:instance smallvar->name-when-member-of-explode-bigvar-to-smallvars
                     (a a) (var var) (varsizes varsizes))
                    (:instance smallvar->name-when-member-of-explode-bigvar-to-smallvars
                     (a a) (var other) (varsizes varsizes)))))

     (local (include-book "centaur/misc/equal-sets" :dir :system))

     (defrule case2-crux
       (iff (intersectp-equal (explode-bigvar-to-smallvars var varsizes)
                              (explode-bigvar-to-smallvars other varsizes))
            (bigvar-equiv var other))
       :in-theory (disable bigvar-equiv)
       :hints((acl2::set-reasoning)))))

  (local
   (defsection case1-crux

     (local (defthm smallenv-lookup-cancel-irrelevant-env-cons
              (implies (not (smallvar-equiv var other))
                       (equal (smallenv-lookup var (cons (cons other val) env))
                              (smallenv-lookup var env)))
              :hints(("Goal" :in-theory (enable smallenv-lookup)))))

     (local (defthm smalleval-list-cancel-irrelevant-env-cons
              (implies (not (member (smallvar-fix irrel-var) (smallvarlist-fix vars)))
                       (equal (smalleval-list (smallexprs-from-smallvars vars)
                                              (cons (cons irrel-var irrel-val)
                                                    env))
                              (smalleval-list (smallexprs-from-smallvars vars) env)))
              :hints(("Goal" :induct (len vars)))))

     (local (defrule smalleval-list-of-pairlis$
              (implies (and (equal (len vars) (len vals))
                            (smallvarlist-p vars)
                            (no-duplicatesp-equal vars))
                       (equal (smalleval-list (smallexprs-from-smallvars vars) (pairlis$ vars vals))
                              (i64list-fix vals)))
              :hints(("Goal"
                      :induct (pairlis$ vars vals)
                      :in-theory (enable smalleval-list pairlis$
                                         smallenv-lookup)))))

     (defrule case1-crux
       (b* ((smallvars (explode-bigvar-to-smallvars bigvar varsizes))
            (smallenv  (explode-bigenv-entry bigvar bigval varsizes))
            (size      (bigvarsize-lookup bigvar varsizes)))
         (equal (bigint->val
                 (smallvals->bigint
                  (smalleval-list (smallexprs-from-smallvars smallvars) smallenv)))
                (logext (* 64 (ceiling size 64)) (bigint->val bigval))))
       :enable (explode-bigenv-entry))))

  (local
   (defrule explode-bigenv-correct-core
     ;; Using logext in the conclusion is a bit ugly, but it is much nicer to do
     ;; it this way than to try to have some kind of bigenv-var-sizeok-p or
     ;; bigenv-sizeok-p hyp.  Why?  Note that we are inducting through the bigenv,
     ;; but we don't have any nice rules about sizeok-p stuff being preserved by
     ;; (cdr bigenv), because shadowed pairs mean there aren't any nice rules
     ;; about it!  Using logext avoids this issue during the inductive part of the
     ;; proof.  Then, we can patch it from the outside to prove the nicer form as
     ;; a corollary.
     (b* ((orig-val   (bigint->val (bigenv-lookup bigvar bigenv)))
          (size       (bigvarsize-lookup bigvar varsizes))
          (smallenv   (explode-bigenv bigenv varsizes))
          (smallvars  (explode-bigvar-to-smallvars bigvar varsizes))
          (smallexprs (smallexprs-from-smallvars smallvars))
          (smallvals  (smalleval-list smallexprs smallenv))
          (new-val    (bigint->val (smallvals->bigint smallvals))))
       (equal new-val
              (logext (* 64 (ceiling size 64)) orig-val)))
     :hints(("Goal"
             :induct (explode-bigenv bigenv varsizes))
            ("Subgoal *1/2"
             :cases ((bigvar-equiv bigvar (caar (bigenv-fix bigenv))))
             :in-theory (enable bigenv-lookup)))))

  ;; The nice, top-level correctness proof just follows directly from the core
  ;; and some very basic arithmetic reasoning about this logext doing nothing
  ;; when the sizes are OK.

  (local (defthm x0
           (implies (posp n)
                    (equal (< (* 64 (ceiling n 64)) n)
                           nil))
           :hints(("Goal"
                   :in-theory (disable lower-bound-of-remultiply-ceiling)
                   :use ((:instance lower-bound-of-remultiply-ceiling
                          (x n)
                          (y 64)))))))

  (local (defrule x1
           (implies (signed-byte-p n bigval)
                    (equal (logext (* 64 (ceiling n 64)) bigval)
                           bigval))
           :enable (signed-byte-p-monotonic)))

  (defrule explode-bigenv-correct
    (implies (bigenv-sizeok-p bigenv varsizes)
             (b* ((orig-val   (bigint->val (bigenv-lookup bigvar bigenv)))
                  (smallenv   (explode-bigenv bigenv varsizes))
                  (smallvars  (explode-bigvar-to-smallvars bigvar varsizes))
                  (smallexprs (smallexprs-from-smallvars smallvars))
                  (smallvals  (smalleval-list smallexprs smallenv))
                  (new-val    (bigint->val (smallvals->bigint smallvals))))
               (equal new-val orig-val)))))



;; i-am-here

;; (defines

;;   (define bigexpr-compile ((x bigexpr-p) ...)
;;          :returns (smallexprs (and (smallexprlist-p smallexprs)
;;                                    (consp smallexprs))
;;                               "A list of smallexprs, least significant to most significant.
;;                           These implement the evaluations of @('x') under
;;                           suitable environments.")
;;          (bigexpr-case x
;;            :var ...
;;            :const (bigint-const-compile x.val)
;;            :call ...))
;;        (define bigexprlist-compile ((x bigexprlist-p) ...)
;;          :returns (ans smallexprlists-p)
;;          (if (

