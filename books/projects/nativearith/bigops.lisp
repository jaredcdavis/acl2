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
(include-book "bignum")
(include-book "i64")
(include-book "ops")
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

(defsection bigops
  :parents (nativearith)
  :short "High-level operations on @(see bignum)s."
  :long "<p>We now implement verified routines for bignum operations such as
comparisons, bitwise operations, arithmetic operations, etc.</p>

<p>This might seem like a silly thing to do since ACL2 and Lisp already provide
bignum arithmetic.  Our motivation is to have clear models of how these
operations can be implemented, which we can then use in our @(see bigexpr) to
@(see expr) compiler.</p>")

(local (xdoc::set-default-parents bigops))

(define bignum-lognot ((a bignum-p))
  :short "Analogue of @(see lognot) for @(see bignum)s."
  :returns (ans bignum-p)
  :measure (bignum-count a)
  :verify-guards nil
  (b* (((bignum a))
       ((bignum b))
       (first (lognot a.first))
       ((when a.endp)
        (bignum-singleton first)))
    (bignum-cons first (bignum-lognot a.rest)))
  ///
  (verify-guards bignum-lognot)

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

  (defrule bignum-lognot-correct
    (equal (bignum-val (bignum-lognot a))
           (lognot (bignum-val a)))
    :induct (bignum-lognot a)
    :expand (bignum-val a)))

(define bignum-logand ((a bignum-p)
                       (b bignum-p))
  :short "Analogue of @(see logand) for @(see bignum)s."
  :returns (ans bignum-p)
  :measure (+ (bignum-count a) (bignum-count b))
  :verify-guards nil
  (b* (((bignum a))
       ((bignum b))
       (first (logand a.first b.first))
       ((when (and a.endp b.endp))
        (bignum-singleton first)))
    (bignum-cons first
                 (bignum-logand a.rest b.rest)))
  ///
  (verify-guards bignum-logand)

  (defrule bignum-logand-correct
    (equal (bignum-val (bignum-logand a b))
           (logand (bignum-val a)
                   (bignum-val b)))
    :induct (two-bignums-induct a b)
    :expand ((bignum-val a)
             (bignum-val b))))

(define bignum-logior ((a bignum-p)
                       (b bignum-p))
  :short "Analogue of @(see logior) for @(see bignum)s."
  :returns (ans bignum-p)
  :measure (+ (bignum-count a) (bignum-count b))
  :verify-guards nil
  (b* (((bignum a))
       ((bignum b))
       (first (logior a.first b.first))
       ((when (and a.endp b.endp))
        (bignum-singleton first)))
    (bignum-cons first
                 (bignum-logior a.rest b.rest)))
  ///
  (verify-guards bignum-logior)

  (defrule bignum-logior-correct
    (equal (bignum-val (bignum-logior a b))
           (logior (bignum-val a)
                   (bignum-val b)))
    :induct (two-bignums-induct a b)
    :expand ((bignum-val a)
             (bignum-val b))))

(define bignum-logxor ((a bignum-p)
                       (b bignum-p))
  :short "Analogue of @(see logxor) for @(see bignum)s."
  :returns (ans bignum-p)
  :measure (+ (bignum-count a) (bignum-count b))
  :verify-guards nil
  (b* (((bignum a))
       ((bignum b))
       (first (logxor a.first b.first))
       ((when (and a.endp b.endp))
        (bignum-singleton first)))
    (bignum-cons first
                 (bignum-logxor a.rest b.rest)))
  ///
  (verify-guards bignum-logxor)

  (defrule bignum-logxor-correct
    (equal (bignum-val (bignum-logxor a b))
           (logxor (bignum-val a)
                   (bignum-val b)))
    :induct (two-bignums-induct a b)
    :expand ((bignum-val a)
             (bignum-val b))))

(define bignum-equalp ((a bignum-p)
                       (b bignum-p))
  :short "Semantic equality of two @(see bignum)s, returning @(see bignum-1) or
@(see bignum-0) for true or false, respectively."
  :long "<p>This is a semantic (not structural) equality check.  That is, the
answer says whether @('a') and @('b') have the same @(see bignum-val)s.</p>"
  :returns (bool booleanp :rule-classes :type-prescription)
  :measure (+ (bignum-count a) (bignum-count b))
  (b* (((bignum a))
       ((bignum b))
       ((unless (eql a.first b.first))
        nil)
       ((when (and a.endp b.endp))
        t))
    (bignum-equalp a.rest b.rest))
  ///
  (defrule bignum-equalp-correct
    (equal (bignum-equalp a b)
           (equal (bignum-val a) (bignum-val b)))
    :induct (two-bignums-induct a b)
    :expand ((bignum-val a)
             (bignum-val b))))

(define bignum-not-equalp ((a bignum-p)
                           (b bignum-p))
  :short "Semantic inequality of two @(see bignum)s, returning @(see bignum-1)
or @(see bignum-0) for true or false, respectively."
  :long "<p>This is a semantic (not structural) equality check.  That is, the
answer says whether @('a') and @('b') have a different @(see bignum-val)s.</p>"
  :returns (bool booleanp :rule-classes :type-prescription)
  :measure (+ (bignum-count a) (bignum-count b))
  (b* (((bignum a))
       ((bignum b))
       ((unless (eql a.first b.first))
        t)
       ((when (and a.endp b.endp))
        nil))
    (bignum-not-equalp a.rest b.rest))
  ///
  (defrule bignum-not-equalp-correct
    (equal (bignum-not-equalp a b)
           (not (equal (bignum-val a) (bignum-val b))))
    :induct (two-bignums-induct a b)
    :expand ((bignum-val a)
             (bignum-val b))))

(define bignum-scmp ((a bignum-p)
                     (b bignum-p))
  :short "Helper for implementing signed comparisons."
  :measure (+ (bignum-count a) (bignum-count b))
  :returns (ans "Says whether @('a') is :equal, :less, or :greater than @('b').")
  (b* (((bignum a))
       ((bignum b))
       ((when (and a.endp b.endp))
        (cond ((eql a.first b.first) :equal)
              ((< a.first b.first)   :less)
              (t                     :greater)))
       (rest-scmp (bignum-scmp a.rest b.rest))
       ((unless (eql rest-scmp :equal))
        rest-scmp)
       ((when (eql a.first b.first))
        :equal)
       ((when (< (loghead 64 a.first)
                 (loghead 64 b.first)))
        :less))
    :greater)
  ///
  (defrule bignum-scmp-correct
    (equal (bignum-scmp a b)
           (let ((av (bignum-val a))
                 (bv (bignum-val b)))
             (cond ((equal av bv) :equal)
                   ((< av bv)     :less)
                   (t             :greater))))
    :induct (two-bignums-induct a b)
    :expand ((bignum-val a)
             (bignum-val b))))

(define bignum-sltp ((a bignum-p)
                     (b bignum-p))
  :short "Signed @(see <) for @(see bignum)s."
  :returns (ans booleanp :rule-classes :type-prescription)
  :measure (+ (bignum-count a) (bignum-count b))
  :verify-guards nil
  (b* (((bignum a))
       ((bignum b))
       ((when (and a.endp b.endp))
        (< a.first b.first))
       (rest-cmp (bignum-scmp a.rest b.rest)))
    (or (eq rest-cmp :less)
        (and (eq rest-cmp :equal)
             (< (loghead 64 a.first)
                (loghead 64 b.first)))))
  ///
  (defrule bignum-sltp-correct
    (equal (bignum-sltp a b)
           (< (bignum-val a) (bignum-val b)))
    :do-not-induct t
    :expand ((bignum-val a)
             (bignum-val b))))

(define bignum-slep ((a bignum-p)
                     (b bignum-p))
  :short "Signed @(see <=) for @(see bignum)s."
  :returns (ans booleanp :rule-classes :type-prescription)
  :measure (+ (bignum-count a) (bignum-count b))
  :verify-guards nil
  (b* (((bignum a))
       ((bignum b))
       ((when (and a.endp b.endp))
        (<= a.first b.first))
       (rest-cmp (bignum-scmp a.rest b.rest)))
    (or (eq rest-cmp :less)
        (and (eq rest-cmp :equal)
             (<= (loghead 64 a.first)
                 (loghead 64 b.first)))))
  ///
  (defrule bignum-slep-correct
    (equal (bignum-slep a b)
           (<= (bignum-val a) (bignum-val b)))
    :do-not-induct t
    :expand ((bignum-val a)
             (bignum-val b))))

(define bignum-sgtp ((a bignum-p)
                     (b bignum-p))
  :short "Signed @(see >) for @(see bignum)s."
  :returns (ans booleanp :rule-classes :type-prescription)
  :measure (+ (bignum-count a) (bignum-count b))
  :verify-guards nil
  (b* (((bignum a))
       ((bignum b))
       ((when (and a.endp b.endp))
        (> a.first b.first))
       (rest-cmp (bignum-scmp a.rest b.rest)))
    (or (eq rest-cmp :greater)
        (and (eq rest-cmp :equal)
             (> (loghead 64 a.first)
                (loghead 64 b.first)))))
  ///
  (defrule bignum-sgtp-correct
    (equal (bignum-sgtp a b)
           (> (bignum-val a) (bignum-val b)))
    :do-not-induct t
    :expand ((bignum-val a)
             (bignum-val b))))

(define bignum-sgep ((a bignum-p)
                     (b bignum-p))
  :short "Signed @(see >=) for @(see bignum)s."
  :returns (ans booleanp :rule-classes :type-prescription)
  :measure (+ (bignum-count a) (bignum-count b))
  :verify-guards nil
  (b* (((bignum a))
       ((bignum b))
       ((when (and a.endp b.endp))
        (>= a.first b.first))
       (rest-cmp (bignum-scmp a.rest b.rest)))
    (or (eq rest-cmp :greater)
        (and (eq rest-cmp :equal)
             (>= (loghead 64 a.first)
                 (loghead 64 b.first)))))
  ///
  (defrule bignum-sgep-correct
    (equal (bignum-sgep a b)
           (>= (bignum-val a) (bignum-val b)))
    :do-not-induct t
    :expand ((bignum-val a)
             (bignum-val b))))
