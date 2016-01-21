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
(include-book "ops")
(include-book "std/util/defrule" :dir :system)
(local (include-book "tools/do-not" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (include-book "misc/assert" :dir :system))
;; (local (include-book "acl2s/cgen/top" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (acl2::do-not generalize fertilize))
(local (in-theory (disable signed-byte-p unsigned-byte-p)))

(local (defrule i64-p-forward
         (implies (i64-p x)
                  (signed-byte-p 64 x))
         :rule-classes :forward-chaining))

(local (defrule i64-p-when-signed-byte-p-64
         (implies (signed-byte-p 64 x)
                  (i64-p x))
         :enable (i64-p)))

(local (defruled logapp-redef
         (equal (logapp n a b)
                (logior (ash b (nfix n))
                        (loghead n a)))
         :enable (ihsext-recursive-redefs
                  ihsext-inductions)))

(local (defrule equal-of-logapp-split
         (implies (integerp x)
                  (equal (equal (logapp n a b) x)
                         (and (equal (loghead n a)
                                     (loghead n x))
                              (equal (ifix b) (ash x (- (nfix n)))))))
         :enable (ihsext-recursive-redefs ihsext-inductions)
         :disable (signed-byte-p)))

(local (defrule equal-of-loghead-ns-when-signed-byte-p-ns
         (implies (and (signed-byte-p n x)
                       (signed-byte-p n y))
                  (equal (equal (loghead n x) (loghead n y))
                         (equal x y)))
         :disable (signed-byte-p)
         :enable (ihsext-inductions
                  ihsext-recursive-redefs)))

(local (defrule equal-loghead-0-when-signed-byte-p
         (implies (signed-byte-p n x)
                  (equal (equal (loghead n x) 0)
                         (equal x 0)))
         :enable (ihsext-recursive-redefs
                  ihsext-inductions)
         :disable (signed-byte-p)))

(local (encapsulate
         ()
         (local (defrule l0
                  ;; Nice general theorem, but doesn't unify nicely with constants
                  (implies (signed-byte-p n x)
                           (equal (equal (loghead n x) (loghead n -1))
                                  (equal x -1)))
                  :induct (signed-byte-p n x)
                  :enable (ihsext-recursive-redefs
                           ihsext-inductions)))

         (make-event
          ;; Special case for 64-bits
          `(defrule equal-loghead-64-minus1-when-signed-byte-p-64
             (implies (signed-byte-p 64 x)
                      (equal (equal (loghead 64 x) ,(loghead 64 -1))
                             (equal x -1)))
             :use ((:instance l0 (n 64)))))))

(local (defrule logtail-n-when-signed-byte-p-n
         (implies (signed-byte-p n x)
                  (equal (logtail n x)
                         (if (< x 0)
                             -1
                           0)))
         :disable (signed-byte-p)
         :enable (ihsext-recursive-redefs ihsext-inductions)))

(local (defrule logapp-of-logext-same
         (equal (logapp n (logext n x) y)
                (logapp n x y))))

(local (defrule equal-of-expanded-logapp
         (implies (natp n)
                  (equal (equal (logior (ash b1 n) (loghead n a1))
                                (logior (ash b2 n) (loghead n a2)))
                         (and (equal (loghead n a1)
                                     (loghead n a2))
                              (equal (ifix b1)
                                     (ifix b2)))))
         :enable (ihsext-recursive-redefs
                  ihsext-inductions)))

(local (defrule equal-of-same-size-logapps
         (equal (equal (logapp 64 a1 b1)
                       (logapp 64 a2 b2))
                (and (equal (loghead 64 a1)
                            (loghead 64 a2))
                     (equal (ifix b1) (ifix b2))))
         :enable logapp-redef))

(local (defrule equal-of-shift-left-and-zero
         (implies (natp n)
                  (equal (equal (ash b n) 0)
                         (equal (ifix b) 0)))
         :enable (ihsext-recursive-redefs
                  ihsext-inductions)))

(local (defrule equal-of-logapp-and-zero
         (equal (equal (logapp n a b) 0)
                (and (equal (loghead n a) 0)
                     (equal (ifix b) 0)))
         :enable logapp-redef))

(local (defrule equal-of-logapp-and-minus1
         (equal (equal (logapp n a b) -1)
                (and (equal (ifix b) -1)
                     (equal (loghead n a) (loghead n -1))))
         :enable (ihsext-recursive-redefs
                  ihsext-inductions)))

(local (defrule logapp-of-loghead-and-logtail
         (equal (logapp n (loghead n x) (logtail n x))
                (ifix x))
         :enable (ihsext-inductions
                  ihsext-recursive-redefs)))

(local (defrule <-of-logapps
         (equal (< (logapp n a1 b1)
                   (logapp n a2 b2))
                (if (< (ifix b1) (ifix b2))
                    t
                  (and (equal (ifix b1) (ifix b2))
                       (< (loghead n a1)
                          (loghead n a2)))))
         :enable (ihsext-recursive-redefs
                  ihsext-inductions)))

(local (defrule <-of-logapp-split
         (implies (integerp x)
                  (equal (< (logapp n a b) x)
                         (if (< (ifix b) (logtail n x))
                             t
                           (and (equal (ifix b) (logtail n x))
                                (< (loghead n a)
                                   (loghead n x))))))
         :disable (<-of-logapps)
         :use ((:instance <-of-logapps
                (a1 a)
                (b1 b)
                (a2 (loghead n x))
                (b2 (logtail n x))))))

(local (defrule <-of-logapp-split-right
         (implies (integerp x)
                  (equal (< x (logapp n a b))
                         (if (< (logtail n x) (ifix b))
                             t
                           (and (equal (ifix b) (logtail n x))
                                (< (loghead n x)
                                   (loghead n a))))))
         :disable (<-of-logapps)
         :use ((:instance <-of-logapps
                (a1 (loghead n x))
                (b1 (logtail n x))
                (a2 a)
                (b2 b)))))



(defxdoc bignum
  :parents (nativearith)
  :short "Explicit representation of bignums as lists of 64-bit integers."
  :long "<p>We now develop a basic representation for bignums by breaking an
integer into a list of 64-bit blocks.</p>

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
@(see bignum-val).</p>")

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
