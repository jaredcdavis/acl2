; Native Arithmetic Library
; Copyright (C) 2015 Kookamara LLC
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
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(include-book "centaur/bitops/fast-logext" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "std/strings/cat" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defxdoc i64ops
  :parents (nativearith)
  :short "Operations on 64-bit signed integers."
  :long "<p>These operations model 64-bit signed integer instructions, i.e.,
they operate on objects that satisfy @('(signed-byte-p 64 x)').</p>

<p>In the logic, each operation fixes its inputs with @(see logext).  Note that
this means all of these operations follows the @(see fty::fty-discipline) for
integers.  For execution performance, each operation is an inlined,
guard-verified function that avoids this fixing with @(see mbe).  But most
Common Lisp systems don't provide full 64-bit fixnums, so these I64 operations
may still not be especially efficient: they may create bignums and may require
using bignum operations.</p>

<p>The arithmetic and logical operations (add, multiply, bitwise and, etc.)
return 64-bit signed integer results, with overflow being truncated using 2's
complement arithmetic as you would expect.</p>

<p>For comparison operators (equality, less than, ...) we return a @(see bitp),
i.e., 1 for true or 0 for false.  This is fine and reasonable, but it is not
clear that it is ideal.  For instance, we might instead use -1 for true and 0
for false, which in some cases might work more nicely with bitwise arithmetic
operations.</p>

<p>I considered using -1 and 0 instead.  Consider for instance:</p>

@({
     long eql_bit (long a, long b) { return (a == b) ? 1 : 0; }
     long eql_signext (long a, long b) { return (a == b) ? -1 : 0; }
})

<p>In isolation, it looks like @('eql_bit') produces slightly shorter/nicer
assembly than @('eql_signext') on X86-64 with GCC 4.8.4 and CLANG 3.5.0.  Of
course that doesn't mean much.  At any rate, if this ever seems important, we
could add alternate versions of these operations that follow the -1 convention,
but for now just using @(see bitp)s seems easy and possibly good.</p>")

(local (xdoc::set-default-parents i64ops))

(defmacro def-i64-cmp2 (name &key short long logic exec)
  `(define ,name ((a integerp :type (signed-byte 64))
                  (b integerp :type (signed-byte 64)))
     :short ,short
     :long ,long
     :returns (ans bitp)
     :inline t
     (mbe :logic
          (b* ((a (logext 64 a))
               (b (logext 64 b)))
            ,logic)
          :exec
          ,exec)
     ///
     (more-returns (ans integerp :rule-classes :type-prescription))
     (defret ,(intern-in-package-of-symbol
               (cat "SIGNED-BYTE-P-64-OF-" (symbol-name name))
               name)
       (signed-byte-p 64 ans))))

(def-i64-cmp2 i64eql
  :short "Equality, i.e., @('a == b'), for signed 64-bit integers."
  :logic (bool->bit (eql a b))
  :exec (if (eql a b) 1 0))

(def-i64-cmp2 i64neq
  :short "Inequality, i.e., @('a != b'), for signed 64-bit integers."
  :logic (bool->bit (not (eql a b)))
  :exec (if (eql a b) 0 1))

(def-i64-cmp2 i64lt
  :short "Less than, i.e., @('a < b'), for signed 64-bit integers."
  :logic (bool->bit (< a b))
  :exec (if (< a b) 1 0))

(def-i64-cmp2 i64leq
  :short "Less than or equal, i.e., @('a <= b'), for signed 64-bit integers."
  :logic (bool->bit (<= a b))
  :exec (if (<= a b) 1 0))

(def-i64-cmp2 i64gt
  :short "Greater than, i.e., @('a > b'), for signed 64-bit integers."
  :logic (bool->bit (> a b))
  :exec (if (> a b) 1 0))

(def-i64-cmp2 i64geq
  :short "Greater than or equal, i.e., @('a >= b'), for signed 64-bit integers."
  :logic (bool->bit (>= a b))
  :exec (if (>= a b) 1 0))




(defmacro def-i64-arith2 (name &key short long logic exec prepwork (inline 't))
  `(define ,name ((a integerp :type (signed-byte 64))
                  (b integerp :type (signed-byte 64)))
     :short ,short
     :long ,long
     :returns (ans integerp :rule-classes :type-prescription)
     :inline ,inline
     :prepwork ,prepwork
     (mbe :logic
          (b* ((a (logext 64 a))
               (b (logext 64 b)))
            ,logic)
          :exec
          ,exec)
     ///
     (defret ,(intern-in-package-of-symbol
               (cat "SIGNED-BYTE-P-64-OF-" (symbol-name name))
               name)
       (signed-byte-p 64 ans))))

(def-i64-arith2 i64bitand
  :short "Bitwise and, i.e., @('a & b'), for signed 64-bit integers."
  :logic (logand a b)
  :exec (logand a b))

(def-i64-arith2 i64bitor
  :short "Bitwise inclusive or, i.e., @('a | b'), for signed 64-bit integers."
  :logic (logior a b)
  :exec (logior a b))

(def-i64-arith2 i64bitxor
  :short "Bitwise exclusive or, i.e., @('a ^ b'), for signed 64-bit integers."
  :logic (logxor a b)
  :exec (logxor a b))


(def-i64-arith2 i64plus
  :short "Addition of @('a + b') for signed 64-bit integers."
  :inline nil
  :logic (logext 64 (+ a b))
  :exec (fast-logext 64 (+ a b)))

(def-i64-arith2 i64minus
  :short "Subtraction of @('a - b') for signed 64-bit integers."
  :inline nil
  :logic (logext 64 (- a b))
  :exec (fast-logext 64 (- a b)))

(def-i64-arith2 i64times
  :short "Multiplication of @('a * b') for signed 64-bit integers."
  :inline nil
  :logic (logext 64 (* a b))
  :exec (fast-logext 64 (* a b)))



(def-i64-arith2 i64div
  :short "Almost: division of @('a / b'), truncating toward 0, for signed
          64-bit integers, but there are subtle corner cases."

  :long "<p>There are two tricky cases here.</p>

<p>First is the obvious possibility of division by 0.  In our semantics,
division by 0 returns 0.</p>

<p>Second is the more subtle boundary case where @('a') is the smallest (``most
negative'') integer and @('b') is -1.  Normally we think of division as
reducing the magnitude of the answer, but of course this doesn't happen when
dividing by 1 or -1.  Unfortunately, this means that @($-2^{63} / -1$) is
@($2^{63}$), which is not a valid 64-bit signed!  In our semantics, we explicitly
define </p>

<p>C compatibility notes.  C99 and C11 both say that dividing by 0 is
undefined.  The C99 standard doesn't address the second boundary case, but the
C11 standard clarifies that it is also undefined: ``if the quotient @('a/b') is
representable ...; otherwise the behavior of both @('a/b') and @('a%b') is
undefined.''  So, to safely implement @('i64div') in C, you will need to
explicitly check that @('b') is nonzero and that either @('b') is not -1 or
@('a') is not @($-2^{63}$).</p>"

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
            :hints(("Goal" :in-theory (enable signed-byte-p)))))))


