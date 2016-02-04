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
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arith"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable signed-byte-p unsigned-byte-p)))

(defxdoc bigint
  :parents (nativearith)
  :short "Explicit representation of arbitrary precision integers based on
lists of 64-bit integers."

  :long "<p>We now develop a representation of big integers where the value of
an integer is broken across a list of 64-bit blocks.</p>

<h3>Internal Representation</h3>

<p>Taking a low level view, the blocks in our representation are arranged in
lsb-first order.  That is, the least significant 64 bits of a number is found
in the @(see car) of the list.  Any more significant bits are found in the
@(see cdr).</p>

<p>To be able to represent signed number can be represented, we interpret the
final (most significant) block by sign-extending it.  Meanwhile, all less
significant blocks are internally represented as signed 64-bit values, but we
interpret them as unsigned when computing the value of the bigint.  Some basic
examples:</p>

@({
        Representation    Interpretation
     -------------------------------------------
       (5 7 9)            5 + 7*2^64 + 9*2^128
       (5 7 -1)           5 + 7*2^64 + -1*2^128
       (-1 7)             (2^64 - 1) + 7*2^64
})

<p>Our representation is non-canonical.  That is, there are bigints that are
equivalent but not equal.  For example:</p>

@({
       (5 7)
       (5 7 0)
       (5 7 0 0)
})

<h3>Low-Level Logical View</h3>

<p>Typically the underlying representation of bigints should not be exposed or
directly used.  Instead, most bigint operations are defined using the following
very low-level wrappers for accessing and iterating through bigints:</p>

<ul>
<li>@(see bigint->endp) &mdash; are we at the end of the bigint?</li>
<li>@(see bigint->first) &mdash; get the least significant 64 bits.</li>
<li>@(see bigint->rest) &mdash; get the remaining bits beyond the first 64.</li>
</ul>

<p>It is often convenient to make use of these accessors via the @('bigint')
@(see b*) binder; @(see patbind-bigint).</p>

<p>The core function for interpreting a bigint as an ordinary ACL2 integer is
@(see bigint->val).</p>


<h3>Higher Level Operations</h3>

<p>We implement many routines for computing with bigints; see @(see bigops)
for details.</p>")

(local (xdoc::set-default-parents bigint))

(define bigint-p (x)
  :short "Recognizer for well-formed bigints."
  :returns (ans booleanp :rule-classes :type-prescription)
  (and (consp x)
       (i64list-p x))
  ///
  (defrule bigint-p-compound-recognizer
    (implies (bigint-p x)
             (and (consp x)
                  (true-listp x)))
    :rule-classes :compound-recognizer))

(defsection bigint-minus1
  :parents (bigint)
  :short "Usual bigint representation of @($-1$)."
  :long "@(def bigint-minus1)"
  (defmacro bigint-minus1 ()
    (list 'quote (list -1))))

(defsection bigint-0
  :parents (bigint)
  :short "Usual bigint representation of @($0$)."
  :long "@(def bigint-0)"
  (defmacro bigint-0 ()
    (list 'quote (list 0))))

(defsection bigint-1
  :parents (bigint)
  :short "Bigint representation of @($1$)."
  :long "@(def bigint-1)"
  (defmacro bigint-1 ()
    (list 'quote (list 1))))

(defsection bigint-64
  :parents (bigint)
  :short "Bigint representation of @($64$)."
  :long "@(def bigint-64)"
  (defmacro bigint-64 ()
    (list 'quote (list 64))))

(defsection bigint-i64max
  :parents (bigint)
  :short "Bigint representation of @(see i64-max)."
  :long "@(def bigint-i64max)"
  (defmacro bigint-i64max ()
    (list 'quote (list (i64-max)))))

(define bigint-fix ((x bigint-p))
  :short "Fixing function for @(see bigint)s."
  :returns (x-fix bigint-p)
  :inline t
  :prepwork ((local (in-theory (enable bigint-p))))
  (mbe :logic
       (if (atom x)
           (bigint-0)
         (i64list-fix x))
       :exec
       x)
  ///
  (defrule bigint-fix-when-bigint-p
    (implies (bigint-p x)
             (equal (bigint-fix x)
                    x)))
  (defrule bigint-fix-of-i64list-fix
    (equal (bigint-fix (i64list-fix x))
           (bigint-fix x))))

(defsection bigint-equiv
  :short "Equivalence relation for @(see bigint)s."

  (deffixtype bigint-equiv
    :pred bigint-p
    :fix bigint-fix
    :equiv bigint-equiv
    :define t
    :forward t)

  (defrefinement i64list-equiv bigint-equiv
    :hints(("Goal"
            ::in-theory (disable bigint-fix-of-i64list-fix)
            :use ((:instance bigint-fix-of-i64list-fix (x x))
                  (:instance bigint-fix-of-i64list-fix (x y)))))))

(define bigint->endp ((x bigint-p))
  :returns (endp booleanp :rule-classes :type-prescription)
  :short "Are we at the end of a bigint?"
  :long "<p>Note that to be able to sign-extend the block list, we say that we
         reach the end once we reach the last block (which is why this isn't
         just @(see atom).</p>"
  :inline t
  (let ((x (bigint-fix x)))
    (atom (cdr x))))

(define bigint->first ((x bigint-p))
  :returns (first i64-p)
  :short "Least significant 64-bit chunk of a bigint."
  :long "<p>We happen to return a 64-bit <b>signed</b> value.  However, unless
         we are at the end of the block list, these 64 bits should really be
         regarded as an unsigned value.</p>"
  :inline t
  :prepwork ((local (in-theory (enable bigint-p))))
  (let ((x (bigint-fix x)))
    (i64-fix (car x)))
  ///
  (defret integerp-of-bigint->first
    (integerp (bigint->first x))
    :rule-classes :type-prescription))

(define bigint->rest ((x bigint-p))
  :returns (rest bigint-p)
  :short "Rest of a list of bigint after skipping past the first chunk.  Or, if
          we've reached the end, we return the 64-bit extension of the sign-bit
          of the final (most significant) block."
  :long "<p>The special handling of the last block allows us to \"cdr\" past
         the end of a block while preserving its value.  This is often useful
         while simultaneously walking down two or more bigint.</p>"
  :prepwork ((local (in-theory (enable bigint-p bigint-fix))))
  (let ((x (bigint-fix x)))
    (if (consp (cdr x))
        (cdr x)
      (let ((first (bigint->first x)))
        (if (< (the (signed-byte 64) first) 0)
            (bigint-minus1)
          (bigint-0))))))

(defsection patbind-bigint
  :short "B* binder for defaggregate-style use of bigint accessors."
  (make-event
   (std::da-make-binder 'bigint '(first rest endp)))
  (defrule patbind-bigint-example
    (b* (((bigint x)))
      (and (equal x.first (bigint->first x))
           (equal x.rest (bigint->rest x))
           (equal x.endp (bigint->endp x))))
    :rule-classes nil))

(define bigint-count ((x bigint-p))
  :returns (count natp :rule-classes :type-prescription)
  :short "Basic measure for recurring down a bigint."
  :measure (len x)
  :prepwork ((local (in-theory (enable bigint->endp
                                       bigint->rest
                                       bigint-fix
                                       bigint-p))))
  (let ((x (bigint-fix x)))
    (if (bigint->endp x)
        0
      (+ 1 (bigint-count (bigint->rest x)))))
  ///
  (defrule bigint-count-when-bigint->endp
    (implies (bigint->endp x)
             (equal (bigint-count x)
                    0)))

  (defrule bigint-count-of-bigint->rest-weak
    (<= (bigint-count (bigint->rest x))
        (bigint-count x))
    :rule-classes :linear)

  (defrule bigint-count-of-bigint->rest-strong
    (implies (not (bigint->endp x))
             (< (bigint-count (bigint->rest x))
                (bigint-count x)))
    :rule-classes :linear))

(define bigint->val ((x bigint-p))
  :returns (val integerp :rule-classes :type-prescription)
  :short "Value of a @(see bigint) as an ordinary ACL2 integer."
  :measure (bigint-count x)
  (if (bigint->endp x)
      (bigint->first x)
    (logapp 64
            (bigint->first x)
            (bigint->val (bigint->rest x))))
  ///
  "<p>Basic structural openers.</p>"

  (defrule bigint->val-when-bigint->endp
    (implies (bigint->endp x)
             (equal (bigint->val x)
                    (bigint->first x))))

  (defrule bigint->val-when-not-bigint->endp
    (implies (not (bigint->endp x))
             (equal (bigint->val x)
                    (logapp 64
                            (bigint->first x)
                            (bigint->val (bigint->rest x))))))

  "<h5>End-Case Reasoning</h5>

   <p>It's crucial to know that when we've reached the end of a bigint, then
   all of the remaining blocks are either @('0') or @('-1').</p>"

  (defrule bigint->val-of-rest-when-first-negative
    (implies (and (< (bigint->first x) 0)
                  (bigint->endp x))
             (equal (bigint->val (bigint->rest x))
                    -1))
    :enable (bigint->endp bigint->first bigint->rest))

  (defrule bigint->val-of-rest-when-first-positive
    (implies (and (<= 0 (bigint->first x))
                  (bigint->endp x))
             (equal (bigint->val (bigint->rest x))
                    0))
    :enable (bigint->endp bigint->first bigint->rest))

  "<p>A more powerful, case-splitting version of the above.  We'll leave this
   disabled by default since it can lead to a lot of case-splitting.</p>"

  (defruled bigint->val-of-rest-split
    (implies (bigint->endp x)
             (equal (bigint->val (bigint->rest x))
                    (if (< (bigint->first x) 0)
                        -1
                      0)))
    :disable (bigint->val))


  "<h5>Special Theorems for Values of 0 and -1</h5>

  <p>Our representation is non-canonical, but a value of @('0') or @('-1') is
  special and implies that all of the first/rest values are going to be fully
  @('0') or @('-1').</p>"

  (defrule bigint->val-of-rest-when-bigint->val-is-zero
    (implies (equal (bigint->val a) 0)
             (equal (bigint->val (bigint->rest a)) 0)))

  (defrule bigint->first-when-bigint->val-is-zero
    (implies (equal (bigint->val a) 0)
             (equal (bigint->first a) 0)))

  (defrule bigint->val-of-rest-when-bigint->val-is-minus1
    (implies (equal (bigint->val a) -1)
             (equal (bigint->val (bigint->rest a)) -1)))

  (defrule bigint->first-when-bigint->val-is-minus1
    (implies (equal (bigint->val a) -1)
             (equal (bigint->first a) -1)))

  "<h5>Basic congruence rules</h5>"
  ;; Proven automatically by the :fix hook.  It just looks weird to have them
  ;; in the documentation without a header.
  )

(define bigint-singleton ((x i64-p))
  :returns (bigint bigint-p)
  :short "Construct the @(see bigint) that represents an arbitrary @(see i64)."
  :inline t
  :prepwork ((local (in-theory (enable bigint-p
                                       bigint->endp
                                       bigint->first
                                       bigint-fix))))
  (list (i64-fix x))
  ///
  (defrule bigint->endp-of-bigint-singleton
    (bigint->endp (bigint-singleton x)))

  (defrule bigint->first-of-bigint-singleton
    (equal (bigint->first (bigint-singleton x))
           (i64-fix x)))

  (defrule bigint->val-of-bigint-singleton
    (equal (bigint->val (bigint-singleton x))
           (i64-fix x)))

  (defrule bigint-count-of-bigint->singleton
    (equal (bigint-count (bigint-singleton x))
           0)))

(define bigint-cons ((first i64-p)
                     (rest  bigint-p))
  :short "Construct the @(see bigint) for @('first | rest << 64')."
  :returns (bigint bigint-p)
  :inline t
  :prepwork ((local (in-theory (enable bigint-p
                                       bigint-fix
                                       bigint->endp
                                       bigint->first
                                       bigint->rest))))
  (cons (i64-fix first)
        (bigint-fix rest))
  ///
  (defrule bigint->first-of-bigint-cons
    (equal (bigint->first (bigint-cons first rest))
           (i64-fix first)))
  (defrule bigint->val-of-bigint-cons
    (equal (bigint->val (bigint-cons first rest))
           (logapp 64 (i64-fix first) (bigint->val rest)))))

(define two-bigints-induct ((a bigint-p)
                            (b bigint-p))
  :short "Basic induction scheme for recurring simultaneously down @('a') and
          @('b') until we're at the end of both."
  :enabled t
  :measure (+ (bigint-count a) (bigint-count b))
  (b* (((bigint a))
       ((bigint b)))
    (if (and a.endp b.endp)
        nil
      (two-bigints-induct a.rest b.rest))))

(define bool->bigint ((x booleanp))
  :returns (num bigint-p)
  :inline t
  (if x
      (bigint-1)
    (bigint-0)))

(define make-bigint ((x integerp))
  :returns (big bigint-p)
  :short "Construct a @(see bigint) that represents any ACL2 integer."
  :verify-guards nil
  :measure (integer-length x)
  (b* ((x (ifix x))
       ((when (i64-p x))
        (bigint-singleton x)))
    (bigint-cons (logext 64 x)
                 (make-bigint (logtail 64 x))))
  :prepwork
  ((local (in-theory (enable i64-p)))

   (local (defrule integer-length-bounded-by-signed-byte-p
            (implies (and (posp n)
                          (signed-byte-p n x))
                     (<= (integer-length x) n))
            :rule-classes ((:linear) (:rewrite))
            :enable (ihsext-inductions ihsext-recursive-redefs)))

   (local (defrule integer-length-lower-bound-when-not-signed-byte-p
            (implies (and (not (signed-byte-p n (ifix x)))
                          (posp n))
                     (<= n (integer-length x)))
            :rule-classes ((:linear) (:rewrite))
            :enable (ihsext-inductions ihsext-recursive-redefs zip))))
  ///
  (verify-guards make-bigint)

  (defthm make-bigint-correct
    (equal (bigint->val (make-bigint x))
           (ifix x))))


(deflist bigintlist
  :elt-type bigint-p
  :true-listp t)

(defprojection bigintlist->vals ((x bigintlist-p))
  :returns (vals integer-listp)
  :nil-preservingp nil
  (bigint->val x))

(define bigintlist-nth ((n natp)
                        (x bigintlist-p))
  :returns (nth bigint-p)
  (mbe :logic (bigint-fix (nth n x))
       :exec
       (or (case n
             (0 (first x))
             (1 (second x))
             (2 (third x))
             (otherwise (nth n x)))
           (bigint-0)))
  :prepwork
  ((local (include-book "arithmetic/top-with-meta" :dir :system))
   (local (include-book "std/lists/nth" :dir :system))
   (local (defthm l0
            (equal (< (+ c a) (+ c b))
                   (< a b))))

   (local (defthm |(< (+ -1 a) b)|
            (equal (< (+ -1 a) b)
                   (< a (+ 1 b)))
            :hints(("Goal"
                    :in-theory (disable l0)
                    :use ((:instance l0 (a (+ -1 a)) (b b) (c 1)))))))

   (local (defthm bigint-p-of-nth-when-bigintlist-p
            (implies (bigintlist-p x)
                     (equal (bigint-p (nth n x))
                            (< (nfix n) (len x))))))

   (local (defthm bigint-fix-of-nth-when-bigintlist-p
            (implies (bigintlist-p x)
                     (equal (bigint-fix (nth n x))
                            (if (< (nfix n) (len x))
                                (nth n x)
                              (bigint-0))))))))

