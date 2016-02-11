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
(include-book "bigops")
(include-book "bigexpr")
(include-book "bigvarsizes")
(include-book "bigeval")
(include-book "maybe-integerp")
(include-book "std/util/defval" :dir :system)
(local (include-book "std/alists/top" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable signed-byte-p)))

(local (xdoc::set-default-parents bigexpr-bound))

(local (defrule signed-byte-p-2-of-bool->bit
         ;; Helper for comparison operations.
         (signed-byte-p 2 (bool->bit x))
         :enable bool->bit))

(local (defrule signed-byte-p-by-integer-length
         ;; This seems like a really nice rule.  BOZO Add to bitops?
         (implies (integerp x)
                  (signed-byte-p (+ 1 (integer-length x)) x))
         :enable (ihsext-recursive-redefs
                  ihsext-inductions)))

(local (defrule posp-when-signed-byte-p-size-forward
         (implies (signed-byte-p size x)
                  (posp size))
         :rule-classes :forward-chaining
         :enable signed-byte-p))


(defprod bigbound
  :short "Static bounding information for a @(see bigexpr)."
  :layout :tree
  :tag nil
  ((size posp "Size bound, as in @(see signed-byte-p), for an expression.")
   (min maybe-integerp "If non-NIL, the (inclusive) minimum value for the expression.")
   (max maybe-integerp "If non-NIL, the (inclusive) maximum value for the expression.")))

(deflist bigboundlist
  :elt-type bigbound
  :true-listp t)


(define bigint-bounded-p ((x bigint-p) (bound bigbound-p))
  :parents (bigbound)
  :short "Check if bounding information is correct for a @(see bigint)."
  (b* ((val (bigint->val x))
       ((bigbound bound)))
    (and (signed-byte-p bound.size val)
         (or (not bound.min) (<= bound.min val))
         (or (not bound.max) (<= val bound.max))))
  ///
  (defrule signed-byte-p-when-bigint-bounded-p
    (implies (bigint-bounded-p x bound)
             (signed-byte-p (bigbound->size bound) (bigint->val x)))
    :rule-classes ((:rewrite) (:forward-chaining)))

  (defrule bigbound-min-linear
    (implies (and (bigint-bounded-p x bound)
                  (bigbound->min bound))
             (<= (bigbound->min bound) (bigint->val x)))
    :rule-classes :linear)

  (defrule bigbound-max-linear
    (implies (and (bigint-bounded-p x bound)
                  (bigbound->max bound))
             (<= (bigint->val x) (bigbound->max bound)))
    :rule-classes :linear)

  (defrule bigint-bounded-p-of-make-bigbound
    (equal (bigint-bounded-p x (make-bigbound :size size :min min :max max))
           (let ((val  (bigint->val x))
                 (size (pos-fix size))
                 (min  (maybe-integerp-fix min))
                 (max  (maybe-integerp-fix max)))
             (and (signed-byte-p size val)
                  (or (not min) (<= min val))
                  (or (not max) (<= val max))))))

  (defrule bigint-bounded-p-with-quotep-bound
    (implies (syntaxp (quotep bound))
             (equal (bigint-bounded-p x bound)
                    (b* ((val (bigint->val x))
                         ((bigbound bound)))
                      (and (signed-byte-p bound.size val)
                           (or (not bound.min) (<= bound.min val))
                           (or (not bound.max) (<= val bound.max))))))))


(define bigintlist-bounded-p ((x bigintlist-p) (bounds bigboundlist-p))
  :guard (equal (len x) (len bounds))
  :short "Check if bounding information is correct for a @(see bigintlist)."
  (if (atom x)
      t
    (and (bigint-bounded-p (car x) (car bounds))
         (bigintlist-bounded-p (cdr x) (cdr bounds))))
  ///
  (defrule bigintlist-bounded-p-when-atom
    (implies (atom x)
             (equal (bigintlist-bounded-p x bounds)
                    t)))
  (defrule bigintlist-bounded-p-of-cons
    (equal (bigintlist-bounded-p (cons a x) bounds)
           (and (bigint-bounded-p a (car bounds))
                (bigintlist-bounded-p x (cdr bounds))))))


(defval *bigbound-for-bit*
  :parents (bigbound)
  :short "A @(see bigbound) for single bits, i.e., 0 or 1."
  (make-bigbound :size 2 :min 0 :max 1))

(defval *bigbound-for-0*
  :parents (bigbound)
  :short "A @(see bigbound) for exactly 0."
  (make-bigbound :size 1 :min 0 :max 0))

(defval *bigbound-for-1*
  :parents (bigbound)
  :short "A @(see bigbound) for exactly 1."
  (make-bigbound :size 2 :min 1 :max 1))


(define bigbound-from-value ((x bigint-p))
  :returns (bound bigbound-p)
  (b* ((val (bigint->val x)))
    (make-bigbound :size (+ 1 (integer-length val))
                   :min val
                   :max val))
  ///
  (defrule bigbound-from-value-correct
    (bigint-bounded-p x (bigbound-from-value x))))


(defsection-progn bigfn-bound-other
  ;; Temporary stub, bozo fixme

  (defstub bigfn-bound-other (* * *) => *)

  (defaxiom bigbound-p-of-bigfn-bound-other
    (bigbound-p (bigfn-bound-other fn args argbounds)))

  (defaxiom bigfn-bound-other-correct
    (implies (bigintlist-bounded-p (bigeval-list args env) argbounds)
             (bigint-bounded-p (bigapply fn (bigeval-list args env))
                               (bigfn-bound-other fn args argbounds))))

  (defrule bigfn-bound-other-correct-alt
    (implies (bigintlist-bounded-p (bigeval-list args env) argbounds)
             (bigint-bounded-p (bigapply fn (bigeval-list args env))
                               (bigfn-bound-other (fn-fix fn)
                                                  (bigexprlist-fix args)
                                                  argbounds)))
    :disable bigfn-bound-other-correct
    :use ((:instance bigfn-bound-other-correct
           (fn (fn-fix fn))
           (args (bigexprlist-fix args))))))



(define bigint-lognot-bound ((arg1   bigexpr-p)
                             (bound1 bigbound-p))
  :returns (bound bigbound-p)
  :short "Infer static bounds for @(see bigint-lognot)."
  (declare (ignorable arg1))
  (b* (((bigbound bound1))
       (new-min (and bound1.max (lognot bound1.max)))
       (new-max (and bound1.min (lognot bound1.min))))
    (make-bigbound :size bound1.size
                   :min new-min
                   :max new-max))
  ///
  (local (defrule l0
           (implies (and (integerp x)
                         (integerp max)
                         (<= x max))
                    (<= (lognot max) (lognot x)))
           :hints(("Goal" :in-theory (enable lognot)))))

  (local (defrule l1
           (implies (and (integerp x)
                         (integerp min)
                         (<= min x))
                    (<= (lognot x) (lognot min)))
           :hints(("Goal" :in-theory (enable lognot)))))

  (defrule bigint-lognot-bound-correct
    (implies (bigint-bounded-p (bigeval arg1 env) bound1)
             (bigint-bounded-p (bigint-lognot (bigeval arg1 env))
                               (bigint-lognot-bound arg1 bound1)))))


(define bigint-logand-bound ((arg1   bigexpr-p)
                             (bound1 bigbound-p)
                             (arg2   bigexpr-p)
                             (bound2 bigbound-p))
  :returns (bound bigbound-p)
  (declare (ignorable arg1 arg2))
  ;; BOZO.  The tau/bounders/elementary-bounders book does something very
  ;; sophisticated for logand.  We probably aren't doing nearly as good of a
  ;; job here.  It may be that we should do better.  For now, I can't stomach
  ;; the thought of depending on such a heavy book.  Maybe we can improve that
  ;; book or redo the proofs in a bitops style?  Also, it looks like
  ;; tau-bounders does some exhaustive exploration of smallish ranges, which
  ;; might be too expensive for our purposes?  We will need to experiment.
  (b* (((bigbound bound1))
       ((bigbound bound2))
       (arg1-natp (and bound1.min (<= 0 bound1.min)))
       (arg2-natp (and bound2.min (<= 0 bound2.min)))
       ((when (or arg1-natp arg2-natp))
        (cond ((and arg1-natp arg2-natp)
               (make-bigbound :size (min bound1.size bound2.size)
                              :min 0
                              :max (and bound1.max bound2.max (max bound1.max bound2.max))))
              (arg1-natp
               (make-bigbound :size bound1.size :min 0 :max bound1.max))
              (t
               (make-bigbound :size bound2.size :min 0 :max bound2.max))))

       (arg1-negp (and bound1.max (< bound1.max 0)))
       (arg2-negp (and bound2.max (< bound2.max 0)))
       ((when (and arg1-negp arg2-negp))
        (make-bigbound :size (max bound1.size bound2.size)
                       :max -1
                       ;; bozo min?
                       )))
    (make-bigbound :size (max bound1.size bound2.size)))
  ///
  (local (defun ind (size1 size2 val1 val2)
           (cond ((or (zp size1) (zp size2))
                  (list size1 size2 val1 val2))
                 ((or (zip val1) (zip val2))
                  nil)
                 ((or (eql val1 -1) (eql val2 -1))
                  nil)
                 (t
                  (ind (- size1 1)
                             (- size2 1)
                             (logcdr val1)
                             (logcdr val2))))))

  (local (defrule l0
           (implies (and (signed-byte-p size1 val1)
                         (signed-byte-p size2 val2)
                         (<= 0 val1)
                         (<= 0 val2))
                    (let ((new-size (min size1 size2)))
                      (signed-byte-p new-size (logand val1 val2))))
           :induct (ind size1 size2 val1 val2)
           :enable (ihsext-inductions ihsext-recursive-redefs)
           :rule-classes ((:rewrite :corollary
                           (implies (and (signed-byte-p size1 val1)
                                         (signed-byte-p size2 val2)
                                         (<= 0 val1)
                                         (<= 0 val2)
                                         (<= size1 size2))
                                    (signed-byte-p size1 (logand val1 val2))))
                          (:rewrite :corollary
                           (implies (and (signed-byte-p size1 val1)
                                         (signed-byte-p size2 val2)
                                         (<= 0 val1)
                                         (<= 0 val2)
                                         (<= size2 size1))
                                    (signed-byte-p size2 (logand val1 val2)))))))

  (local (defrule l1
           (implies (and (signed-byte-p size1 val1)
                         (signed-byte-p size2 val2)
                         (< val1 0)
                         (< val2 0))
                    (let ((new-size (max size1 size2)))
                      (signed-byte-p new-size (logand val1 val2))))
           :induct (ind size1 size2 val1 val2)
           :enable (ihsext-inductions ihsext-recursive-redefs)
           :rule-classes ((:rewrite :corollary
                           (implies (and (signed-byte-p size1 val1)
                                         (signed-byte-p size2 val2)
                                         (< val1 0)
                                         (< val2 0)
                                         (<= size1 size2))
                                    (signed-byte-p size2 (logand val1 val2))))
                          (:rewrite :corollary
                           (implies (and (signed-byte-p size1 val1)
                                         (signed-byte-p size2 val2)
                                         (< val1 0)
                                         (< val2 0)
                                         (<= size2 size1))
                                    (signed-byte-p size1 (logand val1 val2)))))))

  (local (defrule l2
           (implies (and (signed-byte-p size1 val1)
                         (<= 0 val1))
                    (signed-byte-p size1 (logand val1 val2)))
           :induct (ind size1 size2 val1 val2)
           :enable (ihsext-inductions ihsext-recursive-redefs)
           :rule-classes ((:rewrite)
                          (:rewrite :corollary
                           (implies (and (signed-byte-p size2 val2)
                                         (<= 0 val2))
                                    (signed-byte-p size2 (logand val1 val2)))))))

  (defrule bigint-logand-bound-correct
    (implies (and (bigint-bounded-p (bigeval arg1 env) bound1)
                  (bigint-bounded-p (bigeval arg2 env) bound2))
             (bigint-bounded-p (bigint-logand (bigeval arg1 env) (bigeval arg2 env))
                               (bigint-logand-bound arg1 bound1 arg2 bound2)))
    :hints(("Goal" :in-theory (enable bigint-bounded-p)))))


(define bigint-logior-bound ((arg1   bigexpr-p)
                             (bound1 bigbound-p)
                             (arg2   bigexpr-p)
                             (bound2 bigbound-p))
  :returns (bound bigbound-p)
  (declare (ignorable arg1 arg2))
  ;; BOZO horribly stupid!  Improve me!
  (b* (((bigbound bound1))
       ((bigbound bound2)))
    (make-bigbound :size (max bound1.size bound2.size)))
  ///
  (defrule bigint-logior-bound-correct
    (implies (and (bigint-bounded-p (bigeval arg1 env) bound1)
                  (bigint-bounded-p (bigeval arg2 env) bound2))
             (bigint-bounded-p (bigint-logior (bigeval arg1 env) (bigeval arg2 env))
                               (bigint-logior-bound arg1 bound1 arg2 bound2)))
    :hints(("Goal" :in-theory (enable bigint-bounded-p)))))


(define bigint-logxor-bound ((arg1   bigexpr-p)
                             (bound1 bigbound-p)
                             (arg2   bigexpr-p)
                             (bound2 bigbound-p))
  :returns (bound bigbound-p)
  (declare (ignorable arg1 arg2))
  ;; BOZO horribly stupid!  Improve me!
  (b* (((bigbound bound1))
       ((bigbound bound2)))
    (make-bigbound :size (max bound1.size bound2.size)))
  ///
  (defrule bigint-logxor-bound-correct
    (implies (and (bigint-bounded-p (bigeval arg1 env) bound1)
                  (bigint-bounded-p (bigeval arg2 env) bound2))
             (bigint-bounded-p (bigint-logxor (bigeval arg1 env) (bigeval arg2 env))
                               (bigint-logxor-bound arg1 bound1 arg2 bound2)))
    :hints(("Goal" :in-theory (enable bigint-bounded-p)))))


(define bigint-equal-bound ((arg1   bigexpr-p)
                            (bound1 bigbound-p)
                            (arg2   bigexpr-p)
                            (bound2 bigbound-p))
  :returns (bound bigbound-p)
  (declare (ignorable arg1 arg2 bound1 bound2))
  (b* (((bigbound bound1))
       ((bigbound bound2))
       ((when (or (and bound1.max bound2.min (< bound1.max bound2.min))
                  (and bound2.max bound1.min (< bound2.max bound1.min))))
        ;; Equality is impossible because the possible ranges of arg1 and arg2
        ;; don't intersect
        *bigbound-for-0*)
       ((when (and bound1.min bound1.max (eql bound1.min bound1.max)
                   bound2.min bound2.max (eql bound2.min bound2.max)
                   (eql bound1.min bound2.min)))
        ;; Equality is guaranteed because the possible ranges of arg1 and arg2
        ;; constrain them to single values that happen to be identical.
        *bigbound-for-1*))
    *bigbound-for-bit*)
  ///
  (defrule bigint-equal-bound-correct
    (implies (and (bigint-bounded-p (bigeval arg1 env) bound1)
                  (bigint-bounded-p (bigeval arg2 env) bound2))
             (bigint-bounded-p (bigint-equal (bigeval arg1 env) (bigeval arg2 env))
                               (bigint-equal-bound arg1 bound1 arg2 bound2)))
    :hints(("Goal" :in-theory (enable bigint-bounded-p bool->bit)))))


(define bigint-not-equal-bound ((arg1   bigexpr-p)
                                (bound1 bigbound-p)
                                (arg2   bigexpr-p)
                                (bound2 bigbound-p))
  :returns (bound bigbound-p)
  (declare (ignorable arg1 arg2 bound1 bound2))
  (b* (((bigbound bound1))
       ((bigbound bound2))
       ((when (or (and bound1.max bound2.min (< bound1.max bound2.min))
                  (and bound2.max bound1.min (< bound2.max bound1.min))))
        ;; Equality is impossible because the possible ranges of arg1 and arg2
        ;; don't intersect
        *bigbound-for-1*)
       ((when (and bound1.min bound1.max (eql bound1.min bound1.max)
                   bound2.min bound2.max (eql bound2.min bound2.max)
                   (eql bound1.min bound2.min)))
        ;; Equality is guaranteed because the possible ranges of arg1 and arg2
        ;; constrain them to single values that happen to be identical.
        *bigbound-for-0*))
    *bigbound-for-bit*)
  ///
  (defrule bigint-not-equal-bound-correct
    (implies (and (bigint-bounded-p (bigeval arg1 env) bound1)
                  (bigint-bounded-p (bigeval arg2 env) bound2))
             (bigint-bounded-p (bigint-not-equal (bigeval arg1 env) (bigeval arg2 env))
                               (bigint-not-equal-bound arg1 bound1 arg2 bound2)))
    :hints(("Goal" :in-theory (enable bigint-bounded-p bool->bit)))))


(define bigint-<-bound ((arg1   bigexpr-p)
                        (bound1 bigbound-p)
                        (arg2   bigexpr-p)
                        (bound2 bigbound-p))
  :returns (bound bigbound-p)
  (declare (ignorable arg1 arg2 bound1 bound2))
  (b* (((bigbound bound1))
       ((bigbound bound2))
       ((when (and bound1.max bound2.min (< bound1.max bound2.min)))
        ;; arg1 <= max1 < min2 <= arg2
        *bigbound-for-1*)
       ((when (and bound2.max bound1.min (< bound2.max bound1.min)))
        ;; arg2 <= max2 < min1 <= arg1
        *bigbound-for-0*)
       ((when (and bound1.min bound1.max (eql bound1.min bound1.max)
                   bound2.min bound2.max (eql bound2.min bound2.max)))
        ;; both constant, so just compute the answer.
        (if (< bound1.min bound2.min)
            *bigbound-for-1*
          *bigbound-for-0*)))
    *bigbound-for-bit*)
  ///
  (defrule bigint-<-bound-correct
    (implies (and (bigint-bounded-p (bigeval arg1 env) bound1)
                  (bigint-bounded-p (bigeval arg2 env) bound2))
             (bigint-bounded-p (bigint-< (bigeval arg1 env) (bigeval arg2 env))
                               (bigint-<-bound arg1 bound1 arg2 bound2)))
    :hints(("Goal" :in-theory (enable bigint-bounded-p bool->bit)))))


(define bigint-<=-bound ((arg1   bigexpr-p)
                         (bound1 bigbound-p)
                         (arg2   bigexpr-p)
                         (bound2 bigbound-p))
  :returns (bound bigbound-p)
  (declare (ignorable arg1 arg2 bound1 bound2))
  (b* (((bigbound bound1))
       ((bigbound bound2))
       ((when (and bound1.max bound2.min (<= bound1.max bound2.min)))
        ;; arg1 <= max1 <= min2 <= arg2
        *bigbound-for-1*)
       ((when (and bound2.max bound1.min (< bound2.max bound1.min)))
        ;; arg2 <= max2 < min1 <= arg1
        *bigbound-for-0*)
       ((when (and bound1.min bound1.max (eql bound1.min bound1.max)
                   bound2.min bound2.max (eql bound2.min bound2.max)))
        ;; both constant, so just compute the answer.
        (if (<= bound1.min bound2.min)
            *bigbound-for-1*
          *bigbound-for-0*)))
    *bigbound-for-bit*)
  ///
  (defrule bigint-<=-bound-correct
    (implies (and (bigint-bounded-p (bigeval arg1 env) bound1)
                  (bigint-bounded-p (bigeval arg2 env) bound2))
             (bigint-bounded-p (bigint-<= (bigeval arg1 env) (bigeval arg2 env))
                               (bigint-<=-bound arg1 bound1 arg2 bound2)))
    :hints(("Goal" :in-theory (enable bigint-bounded-p bool->bit)))))


(define bigint->-bound ((arg1   bigexpr-p)
                        (bound1 bigbound-p)
                        (arg2   bigexpr-p)
                        (bound2 bigbound-p))
  :returns (bound bigbound-p)
  :inline t
  (bigint-<-bound arg2 bound2 arg1 bound1)
  ///
  (defrule bigint->-bound-correct
    (implies (and (bigint-bounded-p (bigeval arg1 env) bound1)
                  (bigint-bounded-p (bigeval arg2 env) bound2))
             (bigint-bounded-p (bigint-> (bigeval arg1 env) (bigeval arg2 env))
                               (bigint->-bound arg1 bound1 arg2 bound2)))
    :disable (bigint-<-bound-correct)
    :use ((:instance bigint-<-bound-correct
           (arg1 arg2)
           (bound1 bound2)
           (arg2 arg1)
           (bound2 bound1)))))

(define bigint->=-bound ((arg1   bigexpr-p)
                         (bound1 bigbound-p)
                         (arg2   bigexpr-p)
                         (bound2 bigbound-p))
  :returns (bound bigbound-p)
  :inline t
  (bigint-<=-bound arg2 bound2 arg1 bound1)
  ///
  (defrule bigint->=-bound-correct
    (implies (and (bigint-bounded-p (bigeval arg1 env) bound1)
                  (bigint-bounded-p (bigeval arg2 env) bound2))
             (bigint-bounded-p (bigint->= (bigeval arg1 env) (bigeval arg2 env))
                               (bigint->=-bound arg1 bound1 arg2 bound2)))
    :disable (bigint-<=-bound-correct)
    :use ((:instance bigint-<=-bound-correct
           (arg1 arg2)
           (bound1 bound2)
           (arg2 arg1)
           (bound2 bound1)))))


(define bigfn-bound-nth ((n         natp)
                         (args      bigexprlist-p)
                         (argbounds bigboundlist-p))
  :guard (equal (len args) (len argbounds))
  :returns (mv (arg   bigexpr-p)
               (bound bigbound-p))
  (b* ((n (nfix n)))
    (if (< n (len args))
        (mv (bigexpr-fix (nth n args))
            (bigbound-fix (nth n argbounds)))
      (mv (bigexpr-0) *bigbound-for-bit*)))
  ///
  (local (defun ind (n args argbounds)
           (if (zp n)
               (list args argbounds)
             (ind (- n 1) (cdr args) (cdr argbounds)))))

  (local (defrule l0
           (implies (and (< (nfix n) (len args))
                         (bigintlist-bounded-p (bigeval-list args env) argbounds))
                    (bigint-bounded-p (bigeval (nth n args) env)
                                      (nth n argbounds)))
           :induct (ind n args argbounds)))

  (defrule bigfn-bound-nth-is-bounded
    (b* (((mv arg bound) (bigfn-bound-nth n args argbounds)))
      (implies (bigintlist-bounded-p (bigeval-list args env) argbounds)
               (bigint-bounded-p (bigeval arg env) bound))))

  (defruled bigintlist-nth-becomes-eval-of-bigfn-bound-nth
    (b* (((mv arg ?bound) (bigfn-bound-nth n args argbounds)))
      (equal (bigintlist-nth n (bigeval-list args env))
             (bigeval arg env)))
    :in-theory (enable bigintlist-nth nth)
    :induct (nth n args)))


(define bigfn-bound ((fn        fn-p            "Function being applied.")
                     (args      bigexprlist-p   "Arguments it is being applied to.")
                     (argbounds bigboundlist-p "Sizes we have inferred for these arguments."))
  :guard (equal (len args) (len argbounds))
  :returns (bound bigbound-p "Size bound inferred for @('fn(args)').")
  :short "Compute a (possibly overapproximate) size bound for a function call."
  :long "<p>This is the main intelligence behind @(see bigexpr-bound).</p>"
  (b* ((fn        (fn-fix fn))
       (args      (bigexprlist-fix args))
       (argbounds (bigboundlist-fix argbounds)))
    (case fn

      ((bigint-lognot)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds)))
         (bigint-lognot-bound arg1 bound1)))

      ((bigint-equal)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds))
            ((mv arg2 bound2) (bigfn-bound-nth 1 args argbounds)))
         (bigint-equal-bound arg1 bound1 arg2 bound2)))

      ((bigint-not-equal)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds))
            ((mv arg2 bound2) (bigfn-bound-nth 1 args argbounds)))
         (bigint-not-equal-bound arg1 bound1 arg2 bound2)))

      ((bigint-<)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds))
            ((mv arg2 bound2) (bigfn-bound-nth 1 args argbounds)))
         (bigint-<-bound arg1 bound1 arg2 bound2)))

      ((bigint-<=)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds))
            ((mv arg2 bound2) (bigfn-bound-nth 1 args argbounds)))
         (bigint-<=-bound arg1 bound1 arg2 bound2)))

      ((bigint->)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds))
            ((mv arg2 bound2) (bigfn-bound-nth 1 args argbounds)))
         (bigint->-bound arg1 bound1 arg2 bound2)))

      ((bigint->=)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds))
            ((mv arg2 bound2) (bigfn-bound-nth 1 args argbounds)))
         (bigint->=-bound arg1 bound1 arg2 bound2)))

      ((bigint-logand)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds))
            ((mv arg2 bound2) (bigfn-bound-nth 1 args argbounds)))
         (bigint-logand-bound arg1 bound1 arg2 bound2)))

      ((bigint-logior)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds))
            ((mv arg2 bound2) (bigfn-bound-nth 1 args argbounds)))
         (bigint-logior-bound arg1 bound1 arg2 bound2)))

      ((bigint-logxor)
       (b* (((mv arg1 bound1) (bigfn-bound-nth 0 args argbounds))
            ((mv arg2 bound2) (bigfn-bound-nth 1 args argbounds)))
         (bigint-logxor-bound arg1 bound1 arg2 bound2)))

      (otherwise
       (bigfn-bound-other fn args argbounds))))
  ///
  (defrule bigfn-bound-correct
    (implies (bigintlist-bounded-p (bigeval-list args env) argbounds)
             (bigint-bounded-p (bigapply fn (bigeval-list args env))
                               (bigfn-bound fn args argbounds)))
    :enable (bigintlist-nth-becomes-eval-of-bigfn-bound-nth)
    :disable (bigint-equal-correct
              bigint-not-equal-correct
              bigint-<-correct
              bigint-<=-correct
              bigint->-correct
              bigint->=-correct
              )))


(defines bigexpr-bound
  :flag-local nil
  :parents (nativearith)

  (define bigexpr-bound ((x        bigexpr-p     "Expression to evaluate.")
                         (varsizes bigvarsizes-p "Sizes of variables in the expression."))
    :returns (bound bigbound-p "Size bound inferred for @('x').")
    :short "Compute a (possibly overapproximate) size bound for an expression."
    :measure (bigexpr-count x)
    :verify-guards nil
    :flag :expr
    (b* ((x (bigexpr-fix x)))
      (bigexpr-case x
        :const (bigbound-from-value x.val)
        :var   (make-bigbound :size (bigvarsize-lookup x.name varsizes))
        :call  (b* ((argbounds (bigexprlist-bounds x.args varsizes)))
                 (bigfn-bound x.fn x.args argbounds)))))

  (define bigexprlist-bounds ((x        bigexprlist-p)
                              (varsizes bigvarsizes-p))
    :returns (bounds (and (bigboundlist-p bounds)
                          (equal (len bounds) (len x))))
    :measure (bigexprlist-count x)
    :flag :list
    (if (atom x)
        nil
      (cons (bigexpr-bound (car x) varsizes)
            (bigexprlist-bounds (cdr x) varsizes))))

  ///
  (verify-guards bigexpr-bound ::guard-debug t)
  (deffixequiv-mutual bigexpr-bound)

  (defthm-bigexpr-bound-flag
    (defthm bigexpr-bound-correct
      (implies (bigenv-sizeok-p env varsizes)
               (bigint-bounded-p (bigeval x env) (bigexpr-bound x varsizes)))
      :flag :expr
      :hints('(:expand ((bigexpr-bound x varsizes)
                        (bigeval x env)))))
    (defthm bigexprlist-bounds-correct
      (implies (bigenv-sizeok-p env varsizes)
               (bigintlist-bounded-p (bigeval-list x env)
                                     (bigexprlist-bounds x varsizes)))
      :flag :list
      :hints('(:expand ((bigexprlist-bounds x varsizes))))))

  (memoize 'bigexpr-bound :condition '(bigexpr-case x :call)))



