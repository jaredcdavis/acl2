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
(include-book "i64")
(include-book "smallops")
(include-book "std/util/defrule" :dir :system)
(local (include-book "tools/do-not" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "misc/assert" :dir :system))
(local (include-book "arith"))
;; (local (include-book "acl2s/cgen/top" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (acl2::do-not generalize fertilize))
(local (in-theory (disable signed-byte-p unsigned-byte-p)))

(defthm logext-64-of-bfix
  (equal (logext 64 (bfix b))
         (bfix b))
  :hints(("Goal" :in-theory (enable bfix))))

(defthm logext-when-bitp
  (implies (bitp b)
           (equal (logext 64 b)
                  b))
  :hints(("Goal" :in-theory (enable bitp))))


(defsection bigops
  :parents (nativearith)
  :short "High-level operations on @(see bigint)s."
  :long "<p>We now implement verified routines for bigint operations such as
comparisons, bitwise operations, arithmetic operations, etc.</p>

<p>This might seem like a silly thing to do since ACL2 and Lisp already provide
bigint arithmetic.  Our motivation is to have clear models of how these
operations can be implemented, which we can then use in our @(see bigexpr) to
@(see expr) compiler.</p>")

(local (xdoc::set-default-parents bigops))

(define bigint-lognot ((a bigint-p))
  :short "Analogue of @(see lognot) for @(see bigint)s."
  :returns (ans bigint-p)
  :measure (bigint-count a)
  :verify-guards nil
  (b* (((bigint a))
       ((bigint b))
       (first (lognot a.first))
       ((when a.endp)
        (bigint-singleton first)))
    (bigint-cons first (bigint-lognot a.rest)))
  ///
  (verify-guards bigint-lognot)

  (local (defun my-induct (n a)
           (if (zp n)
               (list a)
             (my-induct (- n 1) (logcdr a)))))

  (local (defrule loghead-of-lognot-of-logapp
           ;; BOZO may be a fine rule for ihsext-basics
           (equal (loghead n (lognot (logapp n a b)))
                  (loghead n (lognot a)))
           :induct (my-induct n a)
           :enable (ihsext-inductions
                    ihsext-recursive-redefs)))

  (defrule bigint-lognot-correct
    (equal (bigint->val (bigint-lognot a))
           (lognot (bigint->val a)))
    :induct (bigint-lognot a)
    :expand (bigint->val a)))

(define bigint-logand ((a bigint-p)
                       (b bigint-p))
  :short "Analogue of @(see logand) for @(see bigint)s."
  :returns (ans bigint-p)
  :measure (+ (bigint-count a) (bigint-count b))
  :verify-guards nil
  (b* (((bigint a))
       ((bigint b))
       (first (logand a.first b.first))
       ((when (and a.endp b.endp))
        (bigint-singleton first)))
    (bigint-cons first
                 (bigint-logand a.rest b.rest)))
  ///
  (verify-guards bigint-logand)

  (defrule bigint-logand-correct
    (equal (bigint->val (bigint-logand a b))
           (logand (bigint->val a)
                   (bigint->val b)))
    :induct (two-bigints-induct a b)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-logior ((a bigint-p)
                       (b bigint-p))
  :short "Analogue of @(see logior) for @(see bigint)s."
  :returns (ans bigint-p)
  :measure (+ (bigint-count a) (bigint-count b))
  :verify-guards nil
  (b* (((bigint a))
       ((bigint b))
       (first (logior a.first b.first))
       ((when (and a.endp b.endp))
        (bigint-singleton first)))
    (bigint-cons first
                 (bigint-logior a.rest b.rest)))
  ///
  (verify-guards bigint-logior)

  (defrule bigint-logior-correct
    (equal (bigint->val (bigint-logior a b))
           (logior (bigint->val a)
                   (bigint->val b)))
    :induct (two-bigints-induct a b)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-logxor ((a bigint-p)
                       (b bigint-p))
  :short "Analogue of @(see logxor) for @(see bigint)s."
  :returns (ans bigint-p)
  :measure (+ (bigint-count a) (bigint-count b))
  :verify-guards nil
  (b* (((bigint a))
       ((bigint b))
       (first (logxor a.first b.first))
       ((when (and a.endp b.endp))
        (bigint-singleton first)))
    (bigint-cons first
                 (bigint-logxor a.rest b.rest)))
  ///
  (verify-guards bigint-logxor)

  (defrule bigint-logxor-correct
    (equal (bigint->val (bigint-logxor a b))
           (logxor (bigint->val a)
                   (bigint->val b)))
    :induct (two-bigints-induct a b)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-equalp ((a bigint-p)
                       (b bigint-p))
  :parents (bigint-equal)
  :short "Boolean-valued version of @(see bigint-equal)."
  :returns (bool booleanp :rule-classes :type-prescription)
  :measure (+ (bigint-count a) (bigint-count b))
  (b* (((bigint a))
       ((bigint b))
       ((unless (eql a.first b.first))
        nil)
       ((when (and a.endp b.endp))
        t))
    (bigint-equalp a.rest b.rest))
  ///
  (defrule bigint-equalp-correct
    (equal (bigint-equalp a b)
           (equal (bigint->val a) (bigint->val b)))
    :induct (two-bigints-induct a b)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-equal ((a bigint-p)
                      (b bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @('(equal a b)') for @(see bigint)s."
  :long "<p>This is a semantic (not structural) equality check.  That is, the
answer says whether @('a') and @('b') have the same @(see bigint->val)s.</p>"
  :inline t
  (bool->bigint (bigint-equalp a b))
  ///
  (defrule bigint-equal-correct
    (equal (bigint-equal a b)
           (bool->bigint (equal (bigint->val a) (bigint->val b))))))


(define bigint-not-equalp ((a bigint-p)
                           (b bigint-p))
  :parents (bigint-not-equal)
  :short "Boolean-valued version of @(see bigint-not-equal)."
  :returns (bool booleanp :rule-classes :type-prescription)
  :measure (+ (bigint-count a) (bigint-count b))
  (b* (((bigint a))
       ((bigint b))
       ((unless (eql a.first b.first))
        t)
       ((when (and a.endp b.endp))
        nil))
    (bigint-not-equalp a.rest b.rest))
  ///
  (defrule bigint-not-equalp-correct
    (equal (bigint-not-equalp a b)
           (not (equal (bigint->val a) (bigint->val b))))
    :induct (two-bigints-induct a b)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-not-equal ((a bigint-p)
                          (b bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @('(not (equal a b))') for @(see bigint)s."
  :long "<p>This is a semantic (not structural) equality check.  That is, the
answer says whether @('a') and @('b') have a different @(see bigint->val)s.</p>"
  :inline t
  (bool->bigint (bigint-not-equalp a b))
  ///
  (defrule bigint-not-equal-correct
    (equal (bigint-not-equal a b)
           (bool->bigint (not (equal (bigint->val a) (bigint->val b)))))))


(define bigint-scmp ((a bigint-p)
                     (b bigint-p))
  :parents (bigint-sltp bigint-slep bigint-sgtp bigint-sgep)
  :short "Helper for implementing signed comparisons."
  :measure (+ (bigint-count a) (bigint-count b))
  :returns (ans "Says whether @('a') is :equal, :less, or :greater than @('b').")
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (cond ((eql a.first b.first) :equal)
              ((< a.first b.first)   :less)
              (t                     :greater)))
       (rest-scmp (bigint-scmp a.rest b.rest))
       ((unless (eql rest-scmp :equal))
        rest-scmp)
       ((when (eql a.first b.first))
        :equal)
       ((when (< (loghead 64 a.first)
                 (loghead 64 b.first)))
        :less))
    :greater)
  ///
  (defrule bigint-scmp-correct
    (equal (bigint-scmp a b)
           (let ((av (bigint->val a))
                 (bv (bigint->val b)))
             (cond ((equal av bv) :equal)
                   ((< av bv)     :less)
                   (t             :greater))))
    :induct (two-bigints-induct a b)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-sltp ((a bigint-p)
                     (b bigint-p))
  :returns (ans booleanp :rule-classes :type-prescription)
  :parents (bigint-slt)
  :short "Boolean-valued version of @(see bigint-slt)."
  :measure (+ (bigint-count a) (bigint-count b))
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (< a.first b.first))
       (rest-cmp (bigint-scmp a.rest b.rest)))
    (or (eq rest-cmp :less)
        (and (eq rest-cmp :equal)
             (< (loghead 64 a.first)
                (loghead 64 b.first)))))
  ///
  (defrule bigint-sltp-correct
    (equal (bigint-sltp a b)
           (< (bigint->val a) (bigint->val b)))
    :do-not-induct t
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-slt ((a bigint-p)
                    (b bigint-p))
  :returns (ans bigint-p)
  :short "Signed @(see <) for @(see bigint)s."
  :inline t
  (bool->bigint (bigint-sltp a b))
  ///
  (defrule bigint-slt-correct
    (equal (bigint-slt a b)
           (bool->bigint (< (bigint->val a) (bigint->val b))))))

(define bigint-slep ((a bigint-p)
                     (b bigint-p))
  :parents (bigint-sle)
  :short "Boolean-valued version of @(see bigint-sle)."
  :returns (ans booleanp :rule-classes :type-prescription)
  :measure (+ (bigint-count a) (bigint-count b))
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (<= a.first b.first))
       (rest-cmp (bigint-scmp a.rest b.rest)))
    (or (eq rest-cmp :less)
        (and (eq rest-cmp :equal)
             (<= (loghead 64 a.first)
                 (loghead 64 b.first)))))
  ///
  (defrule bigint-slep-correct
    (equal (bigint-slep a b)
           (<= (bigint->val a) (bigint->val b)))
    :do-not-induct t
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-sle ((a bigint-p)
                    (b bigint-p))
  :returns (ans bigint-p)
  :short "Signed @(see <=) for @(see bigint)s."
  :inline t
  (bool->bigint (bigint-slep a b))
  ///
  (defrule bigint-sle-correct
    (equal (bigint-sle a b)
           (bool->bigint (<= (bigint->val a) (bigint->val b))))))

(define bigint-sgtp ((a bigint-p)
                     (b bigint-p))
  :parents (bigint-sgt)
  :short "Boolean-valued version of @(see bigint-sgt)."
  :returns (ans booleanp :rule-classes :type-prescription)
  :measure (+ (bigint-count a) (bigint-count b))
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (> a.first b.first))
       (rest-cmp (bigint-scmp a.rest b.rest)))
    (or (eq rest-cmp :greater)
        (and (eq rest-cmp :equal)
             (> (loghead 64 a.first)
                (loghead 64 b.first)))))
  ///
  (defrule bigint-sgtp-correct
    (equal (bigint-sgtp a b)
           (> (bigint->val a) (bigint->val b)))
    :do-not-induct t
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-sgt ((a bigint-p)
                    (b bigint-p))
  :returns (ans bigint-p)
  :short "Signed @(see >) for @(see bigint)s."
  :inline t
  (bool->bigint (bigint-sgtp a b))
  ///
  (defrule bigint-sgt-correct
    (equal (bigint-sgt a b)
           (bool->bigint (> (bigint->val a) (bigint->val b))))))

(define bigint-sgep ((a bigint-p)
                     (b bigint-p))
  :parents (bigint-sge)
  :short "Boolean-valued version of @(see bigint-sge)."
  :returns (ans booleanp :rule-classes :type-prescription)
  :measure (+ (bigint-count a) (bigint-count b))
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (>= a.first b.first))
       (rest-cmp (bigint-scmp a.rest b.rest)))
    (or (eq rest-cmp :greater)
        (and (eq rest-cmp :equal)
             (>= (loghead 64 a.first)
                 (loghead 64 b.first)))))
  ///
  (defrule bigint-sgep-correct
    (equal (bigint-sgep a b)
           (>= (bigint->val a) (bigint->val b)))
    :do-not-induct t
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-sge ((a bigint-p)
                    (b bigint-p))
  :returns (ans bigint-p)
  :short "Signed @(see >=) for @(see bigint)s."
  :inline t
  (bool->bigint (bigint-sgep a b))
  ///
  (defrule bigint-sge-correct
    (equal (bigint-sge a b)
           (bool->bigint (>= (bigint->val a) (bigint->val b))))))




(define bigint-plus-cout0 ((cin bitp)
                                  (afirst i64-p)
                                  (bfirst i64-p))
  :short "Determines the carry chain out for adding CIN+A+B by first
          computing CIN+A, then bringing in B afterward."
  :returns (cout bitp)
  :verbosep t
  (b* ((cin     (bfix cin))
       (afirst  (i64-fix afirst))
       (bfirst  (i64-fix bfirst))
       (cin+a   (i64plus cin afirst))
       (usual   (i64upluscarry cin+a bfirst))
       (special (i64bitand (i64eql afirst -1) cin))
       (cout    (i64bitor usual special)))
    cout)

  :prepwork
  ((local (defrule bitp-of-i64upluscarry
            (bitp (i64upluscarry a b))
            :enable (i64upluscarry)))

   (local (defrule bitp-of-i64bitor
            (implies (and (bitp a)
                          (bitp b))
                     (bitp (i64bitor a b)))
            :enable (i64bitor bitp)))

   (local (defrule bitp-of-i64bitand
            (implies (and (bitp a)
                          (bitp b))
                     (bitp (i64bitand a b)))
            :enable (i64bitand bitp))))
  ///
  (deffixequiv bigint-plus-cout0))

(local
 (defsection bigint-plus-cout0-correct
   ;; We put this in its own section to avoid nonlocally depending on plus-ucarryout-n.

   (defrule i64upluscarry-to-plus-ucarryout-n
     (equal (i64upluscarry a b)
            (plus-ucarryout-n 64 0 a b))
     :enable (bigint-plus-cout0 i64upluscarry recursive-plus-correct)
     :disable (plus-ucarryout-n-as-unsigned-byte-p)
     :use ((:instance plus-ucarryout-n-as-unsigned-byte-p
            (n 64) (cin 0) (a (loghead 64 a)) (b (loghead 64 b)))))

   (defrule bigint-plus-cout0-correct
     (equal (bigint-plus-cout0 cin a b)
            (plus-ucarryout-n 64 cin a b))
     :enable (bigint-plus-cout0 i64bitor i64bitand i64eql i64plus i64-fix)
     :use ((:instance plus-carryout-n-using-preadd
            (n 64)
            (cin (bfix cin))
            (a   (logext 64 a)))))))

(define bigint-plus-sum0 ((cin bitp)
                          (afirst i64-p)
                          (bfirst i64-p))
  :returns (sum i64-p)
  (b* ((cin     (lbfix cin))
       (afirst  (i64-fix afirst))
       (bfirst  (i64-fix bfirst))
       (cin+a   (i64plus cin afirst))
       (cin+a+b (i64plus cin+a bfirst)))
    cin+a+b)
  ///
  (local (in-theory (enable i64plus i64-fix)))

  (defthm loghead-64-of-bigint-plus-sum0
    (equal (loghead 64 (bigint-plus-sum0 cin afirst bfirst))
           (loghead 64 (+ (bfix cin)
                          (i64-fix afirst)
                          (i64-fix bfirst))))))

(define bigint-plus-aux ((cin bitp)
                         (a bigint-p)
                         (b bigint-p))
  :returns (ans bigint-p)
  :short "Ripple carry addition of @(see bigint)s."
  :measure (+ (bigint-count a) (bigint-count b))
  :verify-guards nil
  (b* ((cin (lbfix cin))
       ((bigint a))
       ((bigint b))
       (sum0 (bigint-plus-sum0 cin a.first b.first))
       (cout (bigint-plus-cout0 cin a.first b.first))
       ((when (and a.endp b.endp))
        (b* ((asign  (bigint->first a.rest))
             (bsign  (bigint->first b.rest))
             (final  (i64plus cout (i64plus asign bsign))))
          (bigint-cons sum0 (bigint-singleton final)))))
    (bigint-cons sum0
                 (bigint-plus-aux cout a.rest b.rest)))
  ///
  (verify-guards bigint-plus-aux)

  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (in-theory (disable split-plus)))

  (local (defthm base-case
           (implies (and (bigint->endp a) (bigint->endp b))
                    (equal (bigint->val (bigint-plus-aux cin a b))
                           (+ (bfix cin)
                              (bigint->val a)
                              (bigint->val b))))
           :hints(("Goal"
                   :expand (bigint-plus-aux cin a b)
                   :do-not-induct t
                   :do-not '(generalize fertilize)
                   :in-theory (enable i64plus)
                   :use ((:instance split-plus
                          (n 64)
                          (cin (bfix cin))
                          (a (bigint->val a))
                          (b (bigint->val b))))))))

  (local (defthm inductive-case
           (IMPLIES (AND (or (NOT (BIGINT->ENDP A))
                             (NOT (BIGINT->ENDP B)))
                         (EQUAL (BIGINT->VAL (BIGINT-PLUS-AUX (BIGINT-PLUS-COUT0 (BFIX CIN)
                                                                                 (BIGINT->FIRST A)
                                                                                 (BIGINT->FIRST B))
                                                              (BIGINT->REST A)
                                                              (BIGINT->REST B)))
                                (+ (BFIX (BIGINT-PLUS-COUT0 (BFIX CIN)
                                                            (BIGINT->FIRST A)
                                                            (BIGINT->FIRST B)))
                                   (BIGINT->VAL (BIGINT->REST A))
                                   (BIGINT->VAL (BIGINT->REST B)))))
                    (EQUAL (BIGINT->VAL (BIGINT-PLUS-AUX CIN A B))
                           (+ (BFIX CIN)
                              (BIGINT->VAL A)
                              (BIGINT->VAL B))))
           :hints(("Goal"
                   :do-not-induct t
                   :do-not '(generalize fertilize eliminate-destructors)
                   :expand ((bigint-plus-aux cin a b)
                            (bigint->val a)
                            (bigint->val b))
                   :use ((:instance split-plus
                          (n 64)
                          (cin (bfix cin))
                          (a (bigint->val a))
                          (b (bigint->val b))))))))

  (defrule bigint-plus-aux-correct
    (equal (bigint->val (bigint-plus-aux cin a b))
           (+ (bfix cin)
              (bigint->val a)
              (bigint->val b)))
    :hints(("Goal"
            :induct (bigint-plus-aux cin a b))
           ("Subgoal *1/2"
            :in-theory (theory 'minimal-theory)
            :use ((:instance inductive-case)))
           ("Subgoal *1/1"
            :in-theory (theory 'minimal-theory)
            :use ((:instance base-case))))))

(define bigint-plus ((a bigint-p)
                     (b bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see +) for @(see bigint)s."
  (bigint-plus-aux 0 a b)
  ///
  (defthm bigint-plus-correct
    (equal (bigint->val (bigint-plus a b))
           (+ (bigint->val a)
              (bigint->val b)))))

