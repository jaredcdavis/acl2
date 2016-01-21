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
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arith"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable signed-byte-p unsigned-byte-p)))

(defxdoc bignum
  :parents (nativearith)
  :short "Explicit representation of bignums as lists of 64-bit integers."
  :long "<p>We now develop a basic representation for bignums by breaking an
integer into a list of 64-bit blocks.</p>

<h3>Internal Representation</h3>

<p>Taking a low level view, the blocks in our representation are arranged in
lsb-first order.  That is, the least significant 64 bits of a number is found
in the @(see car) of the list.  Any more significant bits are found in the
@(see cdr).</p>

<p>To be able to represent signed number can be represented, we interpret the
final (most significant) block by sign-extending it.  Meanwhile, all less
significant blocks are internally represented as signed 64-bit values, but we
interpret them as unsigned when computing the value of the bignum.  Some basic
examples:</p>

@({
        Representation    Interpretation
     -------------------------------------------
       (5 7 9)            5 + 7*2^64 + 9*2^128
       (5 7 -1)           5 + 7*2^64 + -1*2^128
       (-1 7)             (2^64 - 1) + 7*2^64
})

<p>Our representation is non-canonical.  That is, there are bignums that are
equivalent but not equal.  For example:</p>

@({
       (5 7)
       (5 7 0)
       (5 7 0 0)
})

<h3>Low-Level Logical View</h3>

<p>Typically the underlying representation of bignums should not be exposed or
directly used.  Instead, most bignum operations are defined using the following
very low-level wrappers for accessing and iterating through bignums:</p>

<ul>
<li>@(see bignum->endp) &mdash; are we at the end of the bignum?</li>
<li>@(see bignum->first) &mdash; get the least significant 64 bits.</li>
<li>@(see bignum->rest) &mdash; get the remaining bits beyond the first 64.</li>
</ul>

<p>It is often convenient to make use of these accessors via the @('bignum')
@(see b*) binder; @(see patbind-bignum).</p>

<p>The core function for interpreting a bignum as an ordinary ACL2 integer is
@(see bignum-val).</p>


<h3>Higher Level Operations</h3>

<p>We implement many routines for computing with bignums; see @(see bigops)
for details.</p>")

(local (xdoc::set-default-parents bignum))

(define bignum-p (x)
  :short "Recognizer for well-formed bignums."
  :returns (ans booleanp :rule-classes :type-prescription)
  (and (consp x)
       (i64list-p x))
  ///
  (defrule bignum-p-compound-recognizer
    (implies (bignum-p x)
             (and (consp x)
                  (true-listp x)))
    :rule-classes :compound-recognizer))

(defsection bignum-minus1
  :parents (bignum)
  :short "Usual bignum representation of @($-1$)."
  :long "@(def bignum-minus1)"
  (defmacro bignum-minus1 ()
    (list 'quote (list -1))))

(defsection bignum-0
  :parents (bignum)
  :short "Usual bignum representation of @($0$)."
  :long "@(def bignum-0)"
  (defmacro bignum-0 ()
    (list 'quote (list 0))))

(defsection bignum-1
  :parents (bignum)
  :short "Bignum representation of @($1$)."
  :long "@(def bignum-1)"
  (defmacro bignum-1 ()
    (list 'quote (list 1))))

(define bignum-fix ((x bignum-p))
  :short "Fixing function for @(see bignum)s."
  :returns (x-fix bignum-p)
  :inline t
  :prepwork ((local (in-theory (enable bignum-p))))
  (mbe :logic
       (if (atom x)
           (bignum-0)
         (i64list-fix x))
       :exec
       x)
  ///
  (defrule bignum-fix-when-bignum-p
    (implies (bignum-p x)
             (equal (bignum-fix x)
                    x)))
  (defrule bignum-fix-of-i64list-fix
    (equal (bignum-fix (i64list-fix x))
           (bignum-fix x))))

(defsection bignum-equiv
  :short "Equivalence relation for @(see bignum)s."

  (deffixtype bignum-equiv
    :pred bignum-p
    :fix bignum-fix
    :equiv bignum-equiv
    :define t
    :forward t)

  (defrefinement i64list-equiv bignum-equiv
    :hints(("Goal"
            ::in-theory (disable bignum-fix-of-i64list-fix)
            :use ((:instance bignum-fix-of-i64list-fix (x x))
                  (:instance bignum-fix-of-i64list-fix (x y)))))))

(define bignum->endp ((x bignum-p))
  :returns (endp booleanp :rule-classes :type-prescription)
  :short "Are we at the end of a bignum?"
  :long "<p>Note that to be able to sign-extend the block list, we say that we
         reach the end once we reach the last block (which is why this isn't
         just @(see atom).</p>"
  :inline t
  (let ((x (bignum-fix x)))
    (atom (cdr x))))

(define bignum->first ((x bignum-p))
  :returns (first i64-p)
  :short "Least significant 64-bit chunk of a bignum."
  :long "<p>We happen to return a 64-bit <b>signed</b> value.  However, unless
         we are at the end of the block list, these 64 bits should really be
         regarded as an unsigned value.</p>"
  :inline t
  :prepwork ((local (in-theory (enable bignum-p))))
  (let ((x (bignum-fix x)))
    (i64-fix (car x)))
  ///
  (defret integerp-of-bignum->first
    (integerp (bignum->first x))
    :rule-classes :type-prescription))

(define bignum->rest ((x bignum-p))
  :returns (rest bignum-p)
  :short "Rest of a list of bignum after skipping past the first chunk.  Or, if
          we've reached the end, we return the 64-bit extension of the sign-bit
          of the final (most significant) block."
  :long "<p>The special handling of the last block allows us to \"cdr\" past
         the end of a block while preserving its value.  This is often useful
         while simultaneously walking down two or more bignum.</p>"
  :prepwork ((local (in-theory (enable bignum-p bignum-fix))))
  (let ((x (bignum-fix x)))
    (if (consp (cdr x))
        (cdr x)
      (let ((first (bignum->first x)))
        (if (< (the (signed-byte 64) first) 0)
            (bignum-minus1)
          (bignum-0))))))

(defsection patbind-bignum
  :short "B* binder for defaggregate-style use of bignum accessors."
  (make-event
   (std::da-make-binder 'bignum '(first rest endp)))
  (defrule patbind-bignum-example
    (b* (((bignum x)))
      (and (equal x.first (bignum->first x))
           (equal x.rest (bignum->rest x))
           (equal x.endp (bignum->endp x))))
    :rule-classes nil))

(define bignum-count ((x bignum-p))
  :returns (count natp :rule-classes :type-prescription)
  :short "Basic measure for recurring down a bignum."
  :measure (len x)
  :prepwork ((local (in-theory (enable bignum->endp
                                       bignum->rest
                                       bignum-fix
                                       bignum-p))))
  (let ((x (bignum-fix x)))
    (if (bignum->endp x)
        0
      (+ 1 (bignum-count (bignum->rest x)))))
  ///
  (defrule bignum-count-when-bignum->endp
    (implies (bignum->endp x)
             (equal (bignum-count x)
                    0)))

  (defrule bignum-count-of-bignum->rest-weak
    (<= (bignum-count (bignum->rest x))
        (bignum-count x))
    :rule-classes :linear)

  (defrule bignum-count-of-bignum->rest-strong
    (implies (not (bignum->endp x))
             (< (bignum-count (bignum->rest x))
                (bignum-count x)))
    :rule-classes :linear))

(define bignum-val ((x bignum-p))
  :returns (val integerp :rule-classes :type-prescription)
  :short "Value of a @(see bignum) as an ordinary ACL2 integer."
  :measure (bignum-count x)
  (if (bignum->endp x)
      (bignum->first x)
    (logapp 64
            (bignum->first x)
            (bignum-val (bignum->rest x))))
  ///
  "<p>Basic structural openers.</p>"

  (defrule bignum-val-when-bignum->endp
    (implies (bignum->endp x)
             (equal (bignum-val x)
                    (bignum->first x))))

  (defrule bignum-val-when-not-bignum->endp
    (implies (not (bignum->endp x))
             (equal (bignum-val x)
                    (logapp 64
                            (bignum->first x)
                            (bignum-val (bignum->rest x))))))

  "<h5>End-Case Reasoning</h5>

   <p>It's crucial to know that when we've reached the end of a bignum, then
   all of the remaining blocks are either @('0') or @('-1').</p>"

  (defrule bignum-val-of-rest-when-first-negative
    (implies (and (< (bignum->first x) 0)
                  (bignum->endp x))
             (equal (bignum-val (bignum->rest x))
                    -1))
    :enable (bignum->endp bignum->first bignum->rest))

  (defrule bignum-val-of-rest-when-first-positive
    (implies (and (<= 0 (bignum->first x))
                  (bignum->endp x))
             (equal (bignum-val (bignum->rest x))
                    0))
    :enable (bignum->endp bignum->first bignum->rest))

  "<p>A more powerful, case-splitting version of the above.  We'll leave this
   disabled by default since it can lead to a lot of case-splitting.</p>"

  (defruled bignum-val-of-rest-split
    (implies (bignum->endp x)
             (equal (bignum-val (bignum->rest x))
                    (if (< (bignum->first x) 0)
                        -1
                      0)))
    :disable (bignum-val))


  "<h5>Special Theorems for Values of 0 and -1</h5>

  <p>Our representation is non-canonical, but a value of @('0') or @('-1') is
  special and implies that all of the first/rest values are going to be fully
  @('0') or @('-1').</p>"

  (defrule bignum-val-of-rest-when-bignum-val-is-zero
    (implies (equal (bignum-val a) 0)
             (equal (bignum-val (bignum->rest a)) 0)))

  (defrule bignum->first-when-bignum-val-is-zero
    (implies (equal (bignum-val a) 0)
             (equal (bignum->first a) 0)))

  (defrule bignum-val-of-rest-when-bignum-val-is-minus1
    (implies (equal (bignum-val a) -1)
             (equal (bignum-val (bignum->rest a)) -1)))

  (defrule bignum->first-when-bignum-val-is-minus1
    (implies (equal (bignum-val a) -1)
             (equal (bignum->first a) -1)))

  "<h5>Basic congruence rules</h5>"
  ;; Proven automatically by the :fix hook.  It just looks weird to have them
  ;; in the documentation without a header.
  )

(define bignum-singleton ((x i64-p))
  :returns (bignum bignum-p)
  :short "Construct the @(see bignum) that represents an arbitrary @(see i64)."
  :inline t
  :prepwork ((local (in-theory (enable bignum-p
                                       bignum->endp
                                       bignum->first
                                       bignum-fix))))
  (list (i64-fix x))
  ///
  (defrule bignum->endp-of-bignum-singleton
    (bignum->endp (bignum-singleton x)))

  (defrule bignum->first-of-bignum-singleton
    (equal (bignum->first (bignum-singleton x))
           (i64-fix x)))

  (defrule bignum-val-of-bignum-singleton
    (equal (bignum-val (bignum-singleton x))
           (i64-fix x)))

  (defrule bignum-count-of-bignum->singleton
    (equal (bignum-count (bignum-singleton x))
           0)))

(define bignum-cons ((first i64-p)
                     (rest  bignum-p))
  :short "Construct the @(see bignum) for @('first | rest << 64')."
  :returns (bignum bignum-p)
  :inline t
  :prepwork ((local (in-theory (enable bignum-p
                                       bignum-fix
                                       bignum->endp
                                       bignum->first
                                       bignum->rest))))
  (cons (i64-fix first)
        (bignum-fix rest))
  ///
  (defrule bignum->first-of-bignum-cons
    (equal (bignum->first (bignum-cons first rest))
           (i64-fix first)))
  (defrule bignum-val-of-bignum-cons
    (equal (bignum-val (bignum-cons first rest))
           (logapp 64 (i64-fix first) (bignum-val rest)))))

(define two-bignums-induct ((a bignum-p)
                            (b bignum-p))
  :short "Basic induction scheme for recurring simultaneously down @('a') and
          @('b') until we're at the end of both."
  :enabled t
  :measure (+ (bignum-count a) (bignum-count b))
  (b* (((bignum a))
       ((bignum b)))
    (if (and a.endp b.endp)
        nil
      (two-bignums-induct a.rest b.rest))))
