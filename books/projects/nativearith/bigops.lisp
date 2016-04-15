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
(local (include-book "centaur/bitops/defaults" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "misc/assert" :dir :system))
(local (include-book "arith"))
;; (local (include-book "acl2s/cgen/top" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (acl2::do-not generalize fertilize))
(local (in-theory (disable signed-byte-p unsigned-byte-p)))

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
       (first (i64bitnot a.first))
       ((when a.endp)
        (bigint-singleton first)))
    (bigint-cons first (bigint-lognot a.rest)))
  ///
  (verify-guards bigint-lognot)

  (local (in-theory (enable i64bitnot)))

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
       (first (i64bitand a.first b.first))
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
    :enable (i64bitand)
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
       (first (i64bitor a.first b.first))
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
    :enable (i64bitor)
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
       (first (i64bitxor a.first b.first))
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
    :enable (i64bitxor)
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
       ((unless (bit->bool (i64eql a.first b.first)))
        nil)
       ((when (and a.endp b.endp))
        t))
    (bigint-equalp a.rest b.rest))
  ///
  (defrule bigint-equalp-correct
    (equal (bigint-equalp a b)
           (equal (bigint->val a) (bigint->val b)))
    :induct (two-bigints-induct a b)
    :enable (i64eql)
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
       ((unless (bit->bool (i64eql a.first b.first)))
        t)
       ((when (and a.endp b.endp))
        nil))
    (bigint-not-equalp a.rest b.rest))
  ///
  (defrule bigint-not-equalp-correct
    (equal (bigint-not-equalp a b)
           (not (equal (bigint->val a) (bigint->val b))))
    :induct (two-bigints-induct a b)
    :enable (i64eql)
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
  :parents (bigint-<-p bigint-<=-p bigint->-p bigint->=-p)
  :short "Helper for implementing signed comparisons."
  :measure (+ (bigint-count a) (bigint-count b))
  :returns (ans "Says whether @('a') is :equal, :less, or :greater than @('b').")
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (cond ((bit->bool (i64eql a.first b.first)) :equal)
              ((bit->bool (i64slt a.first b.first)) :less)
              (t                                    :greater)))
       (rest-scmp (bigint-scmp a.rest b.rest))
       ((unless (eql rest-scmp :equal))
        rest-scmp)
       ((when (bit->bool (i64eql a.first b.first)))
        :equal)
       ((when (bit->bool (i64ult a.first b.first)))
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
    :enable (i64eql i64slt i64ult)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-<-p ((a bigint-p)
                    (b bigint-p))
  :returns (ans booleanp :rule-classes :type-prescription)
  :parents (bigint-<)
  :short "Boolean-valued version of @(see bigint-<)."
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (bit->bool (i64slt a.first b.first)))
       (rest-cmp (bigint-scmp a.rest b.rest)))
    (or (eq rest-cmp :less)
        (and (eq rest-cmp :equal)
             (bit->bool (i64ult a.first b.first)))))
  ///
  (defrule bigint-<-p-correct
    (equal (bigint-<-p a b)
           (< (bigint->val a) (bigint->val b)))
    :do-not-induct t
    :enable (i64ult i64slt)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-< ((a bigint-p)
                  (b bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see <) for @(see bigint)s; returns bigint 0 or 1."
  :inline t
  (bool->bigint (bigint-<-p a b))
  ///
  (defrule bigint-<-correct
    (equal (bigint-< a b)
           (bool->bigint (< (bigint->val a) (bigint->val b))))))

(define bigint-<=-p ((a bigint-p)
                     (b bigint-p))
  :parents (bigint-<=)
  :short "Boolean-valued version of @(see bigint-<=)."
  :returns (ans booleanp :rule-classes :type-prescription)
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (bit->bool (i64sle a.first b.first)))
       (rest-cmp (bigint-scmp a.rest b.rest)))
    (or (eq rest-cmp :less)
        (and (eq rest-cmp :equal)
             (bit->bool (i64ule a.first b.first)))))
  ///
  (defrule bigint-<=-p-correct
    (equal (bigint-<=-p a b)
           (<= (bigint->val a) (bigint->val b)))
    :do-not-induct t
    :enable (i64sle i64ule)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-<= ((a bigint-p)
                   (b bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see <=) for @(see bigint)s; returns bigint 0 or 1."
  :inline t
  (bool->bigint (bigint-<=-p a b))
  ///
  (defrule bigint-<=-correct
    (equal (bigint-<= a b)
           (bool->bigint (<= (bigint->val a) (bigint->val b))))))

(define bigint->-p ((a bigint-p)
                    (b bigint-p))
  :parents (bigint->)
  :short "Boolean-valued version of @(see bigint->)."
  :returns (ans booleanp :rule-classes :type-prescription)
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (bit->bool (i64sgt a.first b.first)))
       (rest-cmp (bigint-scmp a.rest b.rest)))
    (or (eq rest-cmp :greater)
        (and (eq rest-cmp :equal)
             (bit->bool (i64ugt a.first b.first)))))
  ///
  (defrule bigint->-p-correct
    (equal (bigint->-p a b)
           (> (bigint->val a) (bigint->val b)))
    :do-not-induct t
    :enable (i64sgt i64ugt)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint-> ((a bigint-p)
                  (b bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see >) for @(see bigint)s; returns bigint 0 or 1."
  :inline t
  (bool->bigint (bigint->-p a b))
  ///
  (defrule bigint->-correct
    (equal (bigint-> a b)
           (bool->bigint (> (bigint->val a) (bigint->val b))))))

(define bigint->=-p ((a bigint-p)
                     (b bigint-p))
  :parents (bigint->=)
  :short "Boolean-valued version of @(see bigint->=)."
  :returns (ans booleanp :rule-classes :type-prescription)
  (b* (((bigint a))
       ((bigint b))
       ((when (and a.endp b.endp))
        (bit->bool (i64sge a.first b.first)))
       (rest-cmp (bigint-scmp a.rest b.rest)))
    (or (eq rest-cmp :greater)
        (and (eq rest-cmp :equal)
             (bit->bool (i64uge a.first b.first)))))
  ///
  (defrule bigint->=-p-correct
    (equal (bigint->=-p a b)
           (>= (bigint->val a) (bigint->val b)))
    :do-not-induct t
    :enable (i64sge i64uge)
    :expand ((bigint->val a)
             (bigint->val b))))

(define bigint->= ((a bigint-p)
                   (b bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see >=) for @(see bigint)s; returns bigint 0 or 1."
  :inline t
  (bool->bigint (bigint->=-p a b))
  ///
  (defrule bigint->=-correct
    (equal (bigint->= a b)
           (bool->bigint (>= (bigint->val a) (bigint->val b))))))


(define bigint-clean ((a bigint-p))
  :short "Clean up a bigint by removing any extra blocks, without changing its value."
  :measure (bigint-count a)
  :returns (ans bigint-p)
  :verify-guards nil
  (b* (((bigint a))
       ((when a.endp)
        ;; Nothing more we can clean up
        (bigint-fix a))
       ((when (and (>= a.first 0)
                   (bigint-equalp a.rest (bigint-0))))
        (bigint-singleton a.first))
       ((when (and (< a.first 0)
                   (bigint-equalp a.rest (bigint-minus1))))
        (bigint-singleton a.first)))
    (bigint-cons a.first (bigint-clean a.rest)))
  ///
  (verify-guards bigint-clean)

  (local (defrule l0
           (implies (and (signed-byte-p 64 a)
                         (<= 0 a))
                    (unsigned-byte-p 63 a))
           :enable (signed-byte-p unsigned-byte-p)))

  (local (defrule l1
           (implies (unsigned-byte-p 63 a)
                    (equal (loghead 64 a)
                           a))))

  (local (in-theory (enable bigint-clean)))

  (defrule bigint-clean-correct
    (equal (bigint->val (bigint-clean a))
           (bigint->val a))))


(define bigint-plus-cout0 ((cin bitp)
                                  (afirst i64-p)
                                  (bfirst i64-p))
  :parents (bigint-plus)
  :short "Determines the carry chain out for adding CIN+A+B by first
          computing CIN+A, then bringing in B afterward."
  :returns (cout bitp)
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
            (n 64)
            (cin 0)
            (a (loghead 64 a))
            (b (loghead 64 b)))))

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
  :parents (bigint-plus)
  :short "Computes the low 64 bits of the result of CIN+A+B."
  :returns (sum i64-p)
  (b* ((cin     (lbfix cin))
       (afirst  (i64-fix afirst))
       (bfirst  (i64-fix bfirst))
       (cin+a   (i64plus cin afirst))
       (cin+a+b (i64plus cin+a bfirst)))
    cin+a+b)
  ///
  (local (in-theory (enable i64plus i64-fix)))

  (defrule bigint-plus-sum0-correct
    (equal (bigint-plus-sum0 cin afirst bfirst)
           (logext 64 (+ (bfix cin)
                         (i64-fix afirst)
                         (i64-fix bfirst))))))

  ;; (defrule loghead-64-of-bigint-plus-sum0
  ;;   (equal (loghead 64 (bigint-plus-sum0 cin afirst bfirst))
  ;;          (loghead 64 (+ (bfix cin)
  ;;                         (i64-fix afirst)
  ;;                         (i64-fix bfirst))))))

(define bigint-plus-aux ((cin bitp)
                         (a bigint-p)
                         (b bigint-p))
  :returns (ans bigint-p)
  :parents (bigint-plus)
  :short "Ripple carry addition of @(see bigint)s with carry in."
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
          ;; We go ahead and clean here because it's very likely that we don't
          ;; actually need the extra block.  This is especially nice so that
          ;; when you look at, e.g., (bigint-plus '(3) '(5)), the answer is
          ;; just '(8) instead of '(8 0), and so forth.
          (bigint-clean (bigint-cons sum0 (bigint-singleton final))))))
    (bigint-cons sum0
                 (bigint-plus-aux cout a.rest b.rest)))
  ///
  (verify-guards bigint-plus-aux)

  (local (include-book "arithmetic/top-with-meta" :dir :system))
  (local (in-theory (disable split-plus)))

  (local (defrule base-case
           (implies (and (bigint->endp a) (bigint->endp b))
                    (equal (bigint->val (bigint-plus-aux cin a b))
                           (+ (bfix cin)
                              (bigint->val a)
                              (bigint->val b))))
           :expand (bigint-plus-aux cin a b)
           :do-not-induct t
           :in-theory (enable i64plus)
           :use ((:instance split-plus
                  (n 64)
                  (cin (bfix cin))
                  (a (bigint->val a))
                  (b (bigint->val b))))))

  (local (defrule inductive-case
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
           :do-not-induct t
           :expand ((bigint-plus-aux cin a b)
                    (bigint->val a)
                    (bigint->val b))
           :use ((:instance split-plus
                  (n 64)
                  (cin (bfix cin))
                  (a (bigint->val a))
                  (b (bigint->val b))))))

  (defrule bigint-plus-aux-correct
    (equal (bigint->val (bigint-plus-aux cin a b))
           (+ (bfix cin)
              (bigint->val a)
              (bigint->val b)))
    :in-theory (union-theories (theory 'minimal-theory)
                               '((:induction bigint-plus-aux)
                                 inductive-case base-case))
    :induct (bigint-plus-aux cin a b)))

(define bigint-plus ((a bigint-p)
                     (b bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see +) for @(see bigint)s."
  (bigint-plus-aux 0 a b)
  ///
  (defrule bigint-plus-correct
    (equal (bigint->val (bigint-plus a b))
           (+ (bigint->val a)
              (bigint->val b)))))

(define bigint-minus ((a bigint-p)
                      (b bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see binary--) for @(see bigint)s."
  (bigint-plus-aux 1 a (bigint-lognot b))
  ///
  (defrule bigint-minus-correct
    (equal (bigint->val (bigint-minus a b))
           (- (bigint->val a)
              (bigint->val b)))
    :use ((:instance bitops::minus-to-lognot (x (bigint->val b))))))

(define bigint-nfix ((n bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see nfix) for @(see bigint)s."
  (if (bigint-<=-p (bigint-0) n)
      (bigint-fix n)
    (bigint-0))
  ///
  (defrule bigint-nfix-correct
    (equal (bigint->val (bigint-nfix n))
           (nfix (bigint->val n)))))

(local (defrule i64-p-of-subtract-64-from-positive
         (implies (and (i64-p n)
                       (<= 0 n))
                  (i64-p (- n 64)))
         :enable (i64-p signed-byte-p)))

;; (local (defrule i64-fix-of-loghead-when-fewer-than-64-bits
;;          (implies (and (<= 0 n)
;;                        (< n 64))
;;                   (equal (i64-fix (loghead n x))
;;                          (loghead n x)))
;;          :enable (i64-fix)
;;          :prep-lemmas
;;          ((defrule logext-64-of-loghead-smaller
;;             (implies (and (<= 0 n) (< n 64))
;;                      (equal (logext 64 (loghead n x))
;;                             (loghead n x)))
;;             :enable (ihsext-inductions ihsext-recursive-redefs)))))

;; (local (defrule i64-fix-when-0-to-64
;;          (implies (and (<= 0 n)
;;                        (<= n 64))
;;                   (equal (i64-fix n)
;;                          (ifix n)))
;;          :enable (i64-fix signed-byte-p)
;;          :disable (acl2::logext-identity)
;;          :use ((:instance acl2::logext-identity (size 64) (i n)))))

(define bigint-loghead-aux ((n i64-p)
                            (a bigint-p))
  :returns (ans bigint-p)
  :parents (bigint-loghead)
  :short "Implementation of @(see bigint-loghead) when we know that @('n') fits
          into 64 bits (to avoid @(see bigint) operations on @('n'))."
  :measure (nfix (i64-fix n))
  :verify-guards nil
  :prepwork ((local (in-theory (enable i64-fix i64slt i64sle i64minus i64loghead))))
  (b* ((n (i64-fix n))
       ((when (bit->bool (i64sle n 64)))
        (cond ((bit->bool (i64sle n 0))
               ;; Special degenerate case, loghead with a negative or zero
               ;; width is just always 0.
               (bigint-0))
              ((bit->bool (i64slt n 64))
               ;; We have enough bits to zero extend in a single chunk.
               (bigint-singleton (i64loghead n (bigint->first a))))
              (t
               ;; Special case where we need another digit because we're right
               ;; at the boundary.  For instance, to zero-extend -1 to 64 bits,
               ;; we need 64 bits of 1s, followed by a zero so that we don't
               ;; interpret the result as negative.
               (bigint-cons (bigint->first a) (bigint-0))))))
    ;; Otherwise, we want more than 64 bits so keep the entire first chunk
    ;; and truncate the tail.

    ;; Extralogical safety valve: it seems pretty unreasonable to create
    ;; numbers that are 2^30 bits or more (that'd be a gigabyte of bits, plus
    ;; cons overhead!)  For comparison, its native bignums, CCL prevents you
    ;; from running (loghead (expt 2 60) -1) and dies with the error: count
    ;; 1152921504606846976 too large for ASH, but it doesn't stop you from
    ;; trying to run (loghead (expt 2 59) -1) and instead reports Memory
    ;; allocation request failed in this case.
    (and (<= (ash 1 30) n)
         (bigint-<-p a (bigint-0))
         (raise "Trying to take ~x0 bits of a negative integer seems like a ~
                 bad idea." n))
    (bigint-cons (bigint->first a)
                 (bigint-loghead-aux (i64minus n 64) (bigint->rest a))))
  ///
  (verify-guards bigint-loghead-aux)

  (local (defrule l0
           (implies (<= n 0)
                    (equal (loghead n a)
                           0))
           :enable (loghead**)))

  (defrule bigint-loghead-aux-correct
    (equal (bigint->val (bigint-loghead-aux n a))
           (loghead (i64-fix n) (bigint->val a)))
    :induct (bigint-loghead-aux n a)
    :expand ((bigint->val a))))

(define bigint-loghead ((n bigint-p)
                        (a bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see loghead) for @(see bigint)s."
  :measure (nfix (bigint->val n))
  :verify-guards nil
  :prepwork ((local (in-theory (enable i64-p signed-byte-p))))
  (b* (((when (bigint-<=-p n (bigint-i64max)))
        (if (bigint-<=-p n (bigint-0))
            (bigint-0)
          (bigint-loghead-aux (bigint->val-when-i64 n) a)))
       ((when (bigint-equalp a (bigint-0)))
        ;; Special hack.  Logically we don't need to do this, but this allows
        ;; us to stop computing things like
        ;;      (bigint-loghead <huge number> '(5))
        ;; as soon as we run out of digits in A, instead of having to walk
        ;; through all of N by 64 bit decrements.
        (bigint-0)))
    ;; Extralogical safety valve, as in bigint-loghead-aux
    (and (bigint-<-p a (bigint-0))
         (raise "Trying to take ~x0 bits of a negative integer seems like a ~
                 bad idea." (bigint->val n)))
    (bigint-cons (bigint->first a)
                 (bigint-loghead (bigint-minus n (bigint-64))
                                 (bigint->rest a))))
  ///
  (verify-guards bigint-loghead)

  (local (defrule l0
           (implies (<= n 0)
                    (equal (loghead n a)
                           0))
           :enable (loghead**)))

  (defrule bigint-loghead-correct
    (equal (bigint->val (bigint-loghead n a))
           (loghead (bigint->val n) (bigint->val a)))
    :induct (bigint-loghead n a)
    :expand ((bigint->val a))))

(define bigint-logext-aux ((n i64-p)
                           (a bigint-p))
  :returns (ans bigint-p)
  :parents (bigint-logext)
  :short "Implementation of @(see bigint-logext) when we know that @('n') fits
          into 64 bits (to avoid @(see bigint) operations on @('n'))."
  :measure (nfix (i64-fix n))
  :verify-guards nil
  :prepwork ((local (in-theory (enable i64-fix i64sle i64slt i64minus i64logcar i64logext))))
  (b* ((n (i64-fix n))
       ((bigint a))
       ((when (bit->bool (i64sle n 64)))
        (cond ((bit->bool (i64sle n 0))
               ;; Special degenerate case, logext with a negative or zero width
               ;; is the sign extension of the lsb.
               (if (bit->bool (i64logcar a.first))
                   (bigint-minus1)
                 (bigint-0)))
              ((bit->bool (i64slt n 64))
               ;; We have enough bits to zero extend in a single chunk.
               (bigint-singleton (i64logext n a.first)))
              (t
               ;; Special case where we need another digit because we're right
               ;; at the boundary.  For instance, to zero-extend -1 to 64 bits,
               ;; we need 64 bits of 1s, followed by a zero so that we don't
               ;; interpret the result as negative.
               (bigint-cons a.first
                            (if (bit->bool (i64slt a.first 0))
                                (bigint-minus1)
                              (bigint-0)))))))
    ;; Otherwise, we want more than 64 bits so keep the entire first chunk
    ;; and sign-extend the tail.

    ;; Extralogical safety valve as in bigint-loghead-aux.
    (and (<= (ash 1 30) n)
         (bigint-<-p a (bigint-0))
         (raise "Trying to take ~x0 bits of a negative integer seems like a ~
                 bad idea." n))
    (bigint-cons a.first
                 (bigint-logext-aux (i64minus n 64) a.rest)))
  ///
  (verify-guards bigint-logext-aux)

  (local (defrule l0
           (implies (<= n 0)
                    (equal (logext n a)
                           (if (bit->bool (logcar a))
                               -1
                             0)))
           :enable (logext**)))

  (local (defrule l1
           (implies (and (signed-byte-p n a)
                         (<= 0 a))
                    (equal (loghead n a)
                           a))
           :enable (ihsext-inductions ihsext-recursive-redefs)))

  (defrule bigint-logext-aux-correct
    (equal (bigint->val (bigint-logext-aux n a))
           (logext (i64-fix n) (bigint->val a)))
    :induct (bigint-logext-aux n a)
    :expand ((bigint->val a))))

(define bigint-logext ((n bigint-p)
                       (a bigint-p))
  :returns (ans bigint-p)
  :short "Analogue of @(see logext) for @(see bigint)s."
  :measure (nfix (bigint->val n))
  :verify-guards nil
  :prepwork ((local (in-theory (enable i64-p signed-byte-p i64logcar))))
  (b* (((when (bigint-<=-p n (bigint-i64max)))
        (if (bigint-<=-p n (bigint-0))
            ;; Special degenerate case of logext by a negative or 0.  We know
            ;; the answer but don't know that N is an i64, so just return it
            ;; directly instead of calling the aux function.
            (if (bit->bool (i64logcar (bigint->first a)))
                (bigint-minus1)
              (bigint-0))
          ;; Else it must be an i64, so call the aux function.
          (bigint-logext-aux (bigint->val-when-i64 n) a)))

       ;; Anything past here should be very rare.
       ((when (bigint-equalp a (bigint-0)))
        ;; Special hack.  Logically we don't need to do this, but this allows
        ;; us to stop computing things like
        ;;      (bigint-logext <huge number> '(5))
        ;; as soon as we run out of digits in A, instead of having to walk
        ;; through all of N by 64 bit decrements.
        (bigint-0))
       ((when (bigint-equalp a (bigint-minus1)))
        ;; Same idea as the special hack above, except for negative A.
        (bigint-minus1)))

    ;; Extralogical safety valve, as in bigint-logext-aux
    (and (bigint-<-p a (bigint-0))
         (raise "Trying to take ~x0 bits of a negative integer seems like a ~
                 bad idea." (bigint->val n)))

    (bigint-cons (bigint->first a)
                 (bigint-logext (bigint-minus n (bigint-64))
                                (bigint->rest a))))
  ///
  (verify-guards bigint-logext)

  (local (defrule l0
           (implies (<= n 0)
                    (equal (logext n a)
                           (if (bit->bool (logcar a))
                               -1
                             0)))
           :enable (logext**)))

  (defrule bigint-logext-correct
    (equal (bigint->val (bigint-logext n a))
           (logext (bigint->val n) (bigint->val a)))
    :induct (bigint-logext n a)
    :expand ((bigint->val a))))





; Implemented:
;
;   lognot
;   logand
;   logior
;   logxor
;   equal
;   not-equal
;   <
;   <=
;   >
;   >=
;   +
;   - (binary)
;   nfix
;   loghead
;   logext
;
;
;
; Not Yet Implemented:
;
;   - (unary)
;   *
;   /
;   %
;   expt
;   clog2
;
;   logbit
;   logapp
;   rsh
;   lsh
;   parity
;   logeqv
;   pos-fix
;   logandc1
;   logandc2
;   logorc1
;   logorc2
;   integer-length
;
;   conversion to/from decimal, hex, binary, octal
;
;   
