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
(include-book "centaur/bitops/fast-logext" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/util/defrule" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/integer-length" :dir :system))
(local (include-book "centaur/bitops/defaults" :dir :system))
(local (include-book "arith"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (enable i64-p i64-fix)))

(defmacro uint64-max ()
  (1- (expt 2 64)))

(defxdoc smallops
  :parents (nativearith)
  :short "Operations on 64-bit signed integers."

  :long "<p>These operations model 64-bit signed integer instructions, i.e.,
they operate on @(see i64) objects.</p>

<p>In the logic, each operation fixes its inputs with @(see i64-fix).  Note
that this means all of these operations follows the @(see fty::fty-discipline)
for 64-bit integers.  For execution performance, each operation is an inlined,
guard-verified function that avoids this fixing with @(see mbe).  But most
Common Lisp systems don't provide full 64-bit fixnums, so these operations may
still not be especially efficient: they may create bignums and may require
using bignum operations.</p>

<p>The arithmetic and logical operations (add, multiply, bitwise and, etc.)
return 64-bit signed integer results, with overflow being truncated using 2's
complement arithmetic as you would expect.</p>

<p>For comparison operators (equality, less than, ...) we return a @(see bitp),
i.e., 1 for true or 0 for false.  We considered instead using -1 for true and 0
for false, which in some cases might work more nicely with bitwise arithmetic
operations, but so far we haven't had a good reason to do it that way.</p>")

(local (xdoc::set-default-parents smallops))


(define i64ite ((a i64-p :type (signed-byte 64))
                (b i64-p :type (signed-byte 64))
                (c i64-p :type (signed-byte 64)))
  :returns (ans integerp :rule-classes :type-prescription)
  :short "64-bit if-then-else, i.e., @('a ? b : c')."
  :long "<p>We return @('b') if @('a') is nonzero, or @('c') otherwise.</p>

  <p>This function is somewhat special because we generally intend for
  @('i64ite') expressions to be evaluated in a lazy fashion.</p>

  <p>Since @('i64ite') is a real function, this lazy evaluation won't occur if
  you call it directly, or if you apply it directly with @(see smallapply).
  However, note that @(see smalleval) has special handling so that we can avoid
  evaluating either @('b') or @('c').  Similarly, our small expression compiler
  treats @('i64ite') operations in a special way, to avoid computing whichever
  branch is not taken.</p>"

  :inline t
  :split-types t
  (mbe :logic
       (b* ((a (logext 64 a))
            (b (logext 64 b))
            (c (logext 64 c)))
         (if (not (eql a 0))
             b
           c))
       :exec
       (if (eql a 0) c b))
  ///
  (more-returns (ans integerp :rule-classes :type-prescription))
  (local (in-theory (disable signed-byte-p)))
  (defret i64-p-of-i64ite
    (i64-p ans)))


(defmacro def-i64-arith1 (name &key short long logic exec prepwork
                               guard-hints (inline 't) (fix 'logext) rest)
  `(define ,name ((a i64-p :type (signed-byte 64)))
     :short ,short
     :long ,long
     :returns (ans integerp :rule-classes :type-prescription)
     :inline ,inline
     :prepwork ,prepwork
     :split-types t
     :guard-hints ,guard-hints
     (mbe :logic
          (b* ((a (,fix 64 a)))
            ,logic)
          :exec
          ,exec)
     ///
     (defret ,(intern-in-package-of-symbol
               (cat "I64-P-OF-" (symbol-name name))
               name)
       (i64-p ans))
     ,@rest))

(def-i64-arith1 i64bitnot
  :short "64-bit integer bitwise complement, i.e., @('~a')."
  :long "<p>Note that this produces the same answer whether @('a') is
         interpreted as signed or unsigned.</p>"
  :logic (lognot a)
  :exec (the (signed-byte 64) (lognot a)))

(def-i64-arith1 i64sminus
  :short "64-bit signed integer negation, i.e., @('-a')."
  :long "<p>Note that the special case of @($-2^{63}$) is @($2^{63}$), which
does not fit as a 64-bit 2's complement integer.  We wrap using the usual
semantics so that @($- (-2^{63})$) is just @($-2^{63}$).</p>"
  :logic (logext 64 (- a))
  :exec (if (eql a (i64-min))
            a
          (the (signed-byte 64) (- a))))

(def-i64-arith1 i64logcar
  :short "64-bit @(see logcar), i.e., the @('a & 1'), i.e., least significant bit."
  :logic (logcar a)
  :exec (the bit (logand a 1))
  :prepwork
  ((local (defrule logand-1-is-logcar
            (equal (logand a 1)
                   (logcar a))
            :enable (ihsext-recursive-redefs)))))

(def-i64-arith1 i64logcdr
  :short "64-bit @(see logcdr), i.e., the <b>arithmetic</b> shift right by 1
          place, sometimes written as @('a >>> 1')."
  :logic (logcdr a)
  :exec (the (signed-byte 64) (ash a -1))
  :prepwork
  ((local (defrule ash-minus1-is-logcdr
            (equal (ash a -1)
                   (logcdr a))
            :enable (ihsext-recursive-redefs)))))


(defmacro def-i64-cmp2 (name &key short long logic exec prepwork
                             guard-hints (fix 'logext) rest)
  `(define ,name ((a i64-p :type (signed-byte 64))
                  (b i64-p :type (signed-byte 64)))
     :short ,short
     :long ,long
     :returns (ans bitp)
     :inline t
     :split-types t
     :prepwork ,prepwork
     :guard-hints ,guard-hints
     (mbe :logic
          (b* ((a (,fix 64 a))
               (b (,fix 64 b)))
            ,logic)
          :exec
          ,exec)
     ///
     (more-returns (ans integerp :rule-classes :type-prescription))
     (defret ,(intern-in-package-of-symbol
               (cat "I64-P-OF-" (symbol-name name))
               name)
       (i64-p ans))
     ,@rest))

(def-i64-cmp2 i64eql
  :short "64-bit integer equality, i.e., @('a == b').  Returns 1 or 0."
  :long "<p>Note that this produces the same answer whether @('a') and @('b')
         are interpreted as signed or unsigned.</p>"
  :logic (bool->bit (eql a b))
  :exec (if (eql a b) 1 0))

(def-i64-cmp2 i64neq
  :short "64-bit integer inequality, i.e., @('a != b').  Returns 1 or 0."
  :long "<p>Note that this produces the same answer whether @('a') and @('b')
         are interpreted as signed or unsigned.</p>"
  :logic (bool->bit (not (eql a b)))
  :exec (if (eql a b) 0 1))

(def-i64-cmp2 i64slt
  :short "64-bit signed integer less than, i.e., @('a < b').  Returns 1 or 0."
  :logic (bool->bit (< a b))
  :exec (if (< a b) 1 0))

(def-i64-cmp2 i64sle
  :short "64-bit signed integer less than or equal, i.e., @('a <= b').  Returns 1 or 0."
  :logic (bool->bit (<= a b))
  :exec (if (<= a b) 1 0))

(def-i64-cmp2 i64sgt
  :short "64-bit signed integer greater than, i.e., @('a > b').  Returns 1 or 0."
  :logic (bool->bit (> a b))
  :exec (if (> a b) 1 0))

(def-i64-cmp2 i64sge
  :short "64-bit signed integer greater than or equal, i.e., @('a >= b').  Returns 1 or 0."
  :logic (bool->bit (>= a b))
  :exec (if (>= a b) 1 0))

(def-i64-cmp2 i64ult
  :short "64-bit unsigned integer less than, i.e., @('a < b').  Returns 1 or 0."
  :fix loghead
  :logic (bool->bit (< a b))
  :exec (if (< (the (unsigned-byte 64) (logand a (uint64-max)))
               (the (unsigned-byte 64) (logand b (uint64-max))))
            1
          0))

(def-i64-cmp2 i64ule
  :short "64-bit unsigned integer less than or equal, i.e., @('a <= b').  Returns 1 or 0."
  :fix loghead
  :logic (bool->bit (<= a b))
  :exec (if (<= (the (unsigned-byte 64) (logand a (uint64-max)))
                (the (unsigned-byte 64) (logand b (uint64-max))))
            1
          0))

(def-i64-cmp2 i64ugt
  :short "64-bit unsigned integer greater than, i.e., @('a > b').  Returns 1 or 0."
  :fix loghead
  :logic (bool->bit (> a b))
  :exec (if (> (the (unsigned-byte 64) (logand a (uint64-max)))
               (the (unsigned-byte 64) (logand b (uint64-max))))
            1
          0))

(def-i64-cmp2 i64uge
  :short "64-bit unsigned integer greater than or equal, @('a >= b').  Returns 1 or 0."
  :fix loghead
  :logic (bool->bit (>= a b))
  :exec (if (>= (the (unsigned-byte 64) (logand a (uint64-max)))
                (the (unsigned-byte 64) (logand b (uint64-max))))
            1
          0))





(defmacro def-i64-arith2 (name &key short long logic exec prepwork
                               guard-hints (inline 't) (fix 'logext) rest)
  `(define ,name ((a i64-p :type (signed-byte 64))
                  (b i64-p :type (signed-byte 64)))
     :short ,short
     :long ,long
     :returns (ans integerp :rule-classes :type-prescription)
     :inline ,inline
     :prepwork ,prepwork
     :guard-hints ,guard-hints
     :split-types t
     ,(if (not exec)
          `(b* ((a (,fix 64 a))
                (b (,fix 64 b)))
             ,logic)
        `(mbe :logic
              (b* ((a (,fix 64 a))
                   (b (,fix 64 b)))
                ,logic)
              :exec
              ,exec))
     ///
     (defret ,(intern-in-package-of-symbol
               (cat "I64-P-OF-" (symbol-name name))
               name)
       (i64-p ans))
     ,@rest))

(def-i64-arith2 i64bitand
  :short "64-bit integer bitwise and, i.e., @('a & b')."
  :long "<p>Note that this produces the same answer whether @('a') and @('b')
         are interpreted as signed or unsigned.</p>"
  :logic (logand a b)
  :exec (logand a b))

(def-i64-arith2 i64bitor
  :short "64-bit integer bitwise inclusive or, i.e., @('a | b')."
  :long "<p>Note that this produces the same answer whether @('a') and @('b')
         are interpreted as signed or unsigned.</p>"
  :logic (logior a b)
  :exec (logior a b))

(def-i64-arith2 i64bitxor
  :short "64-bit integer bitwise exclusive or, i.e., @('a ^ b')."
  :long "<p>Note that this produces the same answer whether @('a') and @('b')
         are interpreted as signed or unsigned.</p>"
  :logic (logxor a b)
  :exec (logxor a b))

(def-i64-arith2 i64loghead
  :short "64-bit integer @(see loghead) operation, i.e., zero extension."
  :long "<p>When @('a') is 64 or greater this just leaves @('b') unchanged.
         When @('a') is negative we just return 0.  Otherwise we zero out the
         most significant portion of @('b') starting at bit @('a').</p>"
  :logic (logext 64 (loghead a b))
  :exec (let ((a-chop
               ;; Loghead will create a huge mask if we give it a huge A.  To
               ;; avoid that (and hence make it possible to even test
               ;; i64loghead against its LLVM counterpart), we explicitly check
               ;; if A is huge and chop it down to a reasonable size if so.
               (cond ((> a 64) 64)
                     ((< a 0) 0)
                     (t a))))
          (fast-logext 64 (loghead a-chop b)))
  :prepwork ((local (in-theory (disable signed-byte-p)))
             (local (defrule l0
                      (implies (and (signed-byte-p n b)
                                    (natp a)
                                    (< n a))
                               (equal (logext n (loghead a b))
                                      b))
                      :disable (signed-byte-p)
                      :enable (ihsext-recursive-redefs
                               ihsext-inductions)))))

(def-i64-arith2 i64logext
  :short "64-bit integer @(see logext) operation, i.e., sign extension."
  :long "<p>When @('a') is 64 or greater this just leaves @('b') unchanged.
         When @('a') is negative we sign extend the least significant bit of
         @('b').  Otherwise we sign extend bit @('b') at position @('a').</p>"
  :logic (logext a b)
  :exec (let ((a-chop
               ;; As in loghead, avoid creating huge masks by chopping down A
               ;; if it's bigger than is sensible.
               (cond ((> a 64) 64)
                     ((<= a 0) 1)
                     (t a))))
          (fast-logext a-chop b))
  :prepwork
  ((local (in-theory (disable signed-byte-p unsigned-byte-p)))

   (local (defrule logext-when-degenerate
            (implies (zp n)
                     (equal (logext n a)
                            (if (bit->bool (logcar a))
                                -1
                              0)))
            :enable (logext**)))

   (local (defrule signed-byte-p-of-logext-when-already-signed-byte-p
            (implies (signed-byte-p n x)
                     (signed-byte-p n (logext m x)))
            :enable (ihsext-inductions ihsext-recursive-redefs)))))

(def-i64-arith2 i64shl
  :short "64-bit integer left-shift operation, i.e., @('a << b')."
  :long "<p>We interpret @('b') as unsigned.  When @('b') is 64 or greater this
         returns zero.  Otherwise we shift @('a') left by @('b') places and
         chop the result back down to 64 bits.</p>"
  :fix loghead
  :logic (logext 64 (ash a b))
  :exec (if (or (>= b 64)
                (< b 0))
            0
          (fast-logext 64 (ash a b)))
  :prepwork ((local (in-theory (disable signed-byte-p unsigned-byte-p)))))

(def-i64-arith2 i64lshr
  :short "64-bit integer logical right-shift operation, i.e., @('a >> b')."
  :long "<p>We interpret @('b') as unsigned.  When @('b') is 64 or greater this
         returns zero.  Otherwise we shift @('a') right by @('b') places and
         chop the result back down to 64 bits.  This is a logical shift, not an
         arithmetic shift, i.e., we shift in 0s regardless of the sign bit of
         @('a').</p>"
  :fix loghead
  :logic (logext 64 (ash a (- b)))
  :exec (if (or (>= b 64)
                (< b 0))
            0
          (fast-logext 64 (ash (loghead 64 a) (- b))))
  :prepwork
  ((local (in-theory (disable signed-byte-p unsigned-byte-p)))
   (local (defthm loghead-default-1-unlimited
            (implies (not (natp n))
                     (equal (loghead n x)
                            0))))))

(def-i64-arith2 i64ashr
  :short "64-bit integer arithmetic right-shift operation, i.e., @('a >>> b')."
  :long "<p>We interpret @('b') as unsigned.  When @('b') is 64 or greater this
         returns either -1 or 0, depending on the sign of @('a').  Otherwise we
         arithmetically shift @('a') right by @('b') places, and chop the
         result back down to 64 bits.</p>"
  :fix loghead
  :logic (ash (logext 64 a) (- b))
  :exec (if (or (>= b 64)
                (< b 0))
            (if (< a 0) -1 0)
          (ash a (- b)))
  :prepwork
  ((local (in-theory (disable signed-byte-p unsigned-byte-p)))))


(def-i64-arith2 i64plus
  :short "64-bit integer addition, i.e., @('a + b')."
  :long "<p>Note that this produces the same answer whether @('a') and @('b')
         are interpreted as signed or unsigned.</p>"
  :inline nil
  :logic (logext 64 (+ a b))
  :exec (fast-logext 64 (+ a b)))

(def-i64-arith2 i64upluscarry
  :short "Carry out from 64-bit unsigned integer addition."
  :long "<p>This computes whether a 64-bit unsigned addition overflows.</p>"
  :inline nil
  :fix loghead
  :logic (bool->bit (not (unsigned-byte-p 64 (+ a b))))
  :exec  (let ((a (loghead 64 a))
               (b (loghead 64 b)))
           (if (< (+ a b) (expt 2 64))
               0
             1)))

(def-i64-arith2 i64minus
  :short "64-bit integer subtraction, i.e., @('a - b')."
  :long "<p>Note that this produces the same answer whether @('a') and @('b')
         are interpreted as signed or unsigned.</p>"
  :inline nil
  :logic (logext 64 (- a b))
  :exec (fast-logext 64 (- a b)))

(def-i64-arith2 i64times
  :short "64-bit integer multiplication, i.e., @('a * b')."
  :long "<p>Note that this produces the same answer whether @('a') and @('b')
         are interpreted as signed or unsigned.  To verify this, consider for
         instance the following theorem:</p>
           @(def i64times-signedness-irrelevant)"
  :inline nil
  :logic (logext 64 (* a b))
  :exec (fast-logext 64 (* a b))
  :rest
  ((defthm i64times-signedness-irrelevant
     (implies (and (i64-p a)
                   (i64-p b))
              (let ((signed-ans   (logext 64 (* a b)))
                    (unsigned-ans (loghead 64 (* (loghead 64 a)
                                                 (loghead 64 b)))))
                (equal signed-ans
                       (logext 64 unsigned-ans))))
     :rule-classes nil)))

(def-i64-arith2 i64sdiv
  :short "64-bit signed integer division, i.e., @('a / b'), with truncation
toward zero.  Well, almost&mdash;there are some subtle corner cases."

  :long "<p>Our ACL2 specification is based on the @(see truncate) function,
which per the ACL2 documentation rounds towards zero.</p>

<p>There are two tricky cases here.</p>

<p>First is the obvious possibility of division by 0.  In our semantics,
division by 0 returns 0.</p>

<p>Second is the more subtle boundary case where @('a') is the smallest (``most
negative'') integer and @('b') is -1.  Normally we think of division as
reducing the magnitude of the answer, but of course this doesn't happen when
dividing by 1 or -1.  Unfortunately, this means that @($-2^{63} / -1$) is
@($2^{63}$), which is not a valid 64-bit signed!  We explicitly define
@($-2^{63} / -1$) as @($-2^{63}$), which is arguably the most correct thing to
do.</p>

<p>Some illustrative examples:</p>

@(def i64sdiv-examples)

<p><b>C compatibility notes</b>.  C99 and C11 both say that dividing by 0 is
undefined.  The C99 standard doesn't address the second boundary case, but the
C11 standard clarifies that it is also undefined: ``if the quotient @('a/b') is
representable ...; otherwise the behavior of both @('a/b') and @('a%b') is
undefined.''  So, to safely implement @('i64div') in C, you will need to
explicitly check that @('b') is nonzero and that either @('b') is not -1 or
@('a') is not @($-2^{63}$).</p>

<p><b>LLVM compatibility notes</b>.  The LLVM language reference manual (at
least for LLVM 3.8) explains that division by zero is undefined and that
overflow is also undefined.  A proper LLVM implementation therefore requires
explicit checking that we are not dividing @($-2^{63}$) by @($-1$).</p>"
  :inline nil
  :logic (logext 64 (truncate a b))
  :exec (cond ((eql b 0)
               0)
              ((and (eql b -1)
                    (eql a (- (expt 2 63))))
               a)
              (t
               (the (signed-byte 64) (truncate a b))))
  :prepwork
  ((local (include-book "arithmetic/top" :dir :system))
   (local (in-theory (e/d (bitops::basic-signed-byte-p-of-truncate-split)
                          (truncate signed-byte-p))))

   (local (defthm truncate-of-minus-1
            (implies (integerp a)
                     (equal (truncate a -1) (- a)))
            :hints(("Goal" :in-theory (enable truncate)))))

   (local (defthm truncate-of-zero
            (equal (truncate a 0) 0)
            :hints(("Goal" :in-theory (enable truncate)))))

   (local (defthm logext-helper
            (implies (signed-byte-p 64 a)
                     (equal (logext 64 (- a))
                            (if (equal a (- (expt 2 63)))
                                (- (expt 2 63))
                              (- a))))
            :hints(("Goal" :in-theory (enable signed-byte-p))))))
  :rest
  ((defthm i64sdiv-examples
     (and
      ;; To show that it rounds towards zero
      (equal (i64sdiv 5 3) 1)
      (equal (i64sdiv -5 3) -1)
      (equal (i64sdiv 0 0) 0)
      (equal (i64sdiv 5 0) 0)
      (equal (i64sdiv -5 0) 0)
      (equal (i64sdiv (- (expt 2 63)) -1)
             (- (expt 2 63))))
     :rule-classes nil)))


(def-i64-arith2 i64udiv
  :short "64-bit unsigned integer division, i.e., @('a / b'), truncating any
fractional part.  Division by zero returns zero."

  :long "<p>This is much simpler than @(see i64sdiv) because there is no way
for unsigned division to overflow.  Division by zero is still a problem: in our
semantics it explicitly returns 0.</p>"
  :inline nil
  :fix loghead
  :logic (logext 64 (truncate a b))
  :exec (cond ((eql b 0)
               0)
              (t
               (fast-logext 64 (truncate (logand (the (signed-byte 64) a) (uint64-max))
                                         (logand (the (signed-byte 64) b) (uint64-max))))))
  :prepwork
  ((local (include-book "arithmetic/top" :dir :system))
   (local (in-theory (disable truncate signed-byte-p unsigned-byte-p)))

   (local (defthm truncate-of-zero
            (equal (truncate a 0) 0)
            :hints(("Goal" :in-theory (enable truncate)))))

   (local (defthm equal-of-loghead-and-zero-when-signed-byte-p
            (implies (signed-byte-p n b)
                     (equal (equal (loghead n b) 0)
                            (equal b 0)))
            :hints(("Goal"
                    :induct (signed-byte-p n b)
                    :in-theory (e/d* (bitops::ihsext-inductions
                                      bitops::ihsext-recursive-redefs)
                                     (signed-byte-p loghead))))))))


;; BOZO replace this with proper llvm urem/srem based stuff.
;; Careful for overflow and zero division.

;; (def-i64-arith2 i64rem
;;   :short "Almost: remainder of @('a / b'), truncating toward 0, for signed
;; 64-bit integers, but note there are subtle corner cases."

;;   :long "<p>The C standard defines </p>"

;;   :inline nil
;;   :logic (logext 64 (rem a b))
;;   :exec (cond ((eql b 0)
;;                a)
;;               (t
;;                (the (signed-byte 64) (rem a b))))
;;   :prepwork
;;   ((local (in-theory (disable rem)))

;;    (local (defthm rem-of-zero
;;             (implies (integerp a)
;;                      (equal (rem a 0) (ifix a)))
;;             :hints(("Goal" :in-theory (enable rem)))))))



