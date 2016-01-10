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
64-bit integers, but note there are subtle corner cases."

  :long "<p>There are two tricky cases here.</p>

<p>First is the obvious possibility of division by 0.  In our semantics,
division by 0 returns 0.</p>

<p>Second is the more subtle boundary case where @('a') is the smallest (``most
negative'') integer and @('b') is -1.  Normally we think of division as
reducing the magnitude of the answer, but of course this doesn't happen when
dividing by 1 or -1.  Unfortunately, this means that @($-2^{63} / -1$) is
@($2^{63}$), which is not a valid 64-bit signed!  In our semantics, we
explicitly define @($-2^{63} / -1$) as @($-2^{63}$), which is arguably the most
correct thing to do.</p>

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


(def-i64-arith2 i64rem
  :short "Almost: remainder of @('a / b'), truncating toward 0, for signed
64-bit integers, but note there are subtle corner cases."

  :long "<p>The C standard defines </p>"

  :inline nil
  :logic (logext 64 (rem a b))
  :exec (cond ((eql b 0)
               a)
              (t
               (the (signed-byte 64) (rem a b))))
  :prepwork
  ((local (in-theory (disable rem)))

   (local (defthm rem-of-zero
            (implies (integerp a)
                     (equal (rem a 0) (ifix a)))
            :hints(("Goal" :in-theory (enable rem)))))))



; BOZO remainder -- prove correctness with respect to C spec

; BOZO shift operations.  E1 << E2 or E1 >> E2
;
;   If the value of the E2 is negative OR is greater than or equal to the width
;   of the promoted E1, the behavior is undefined.
;
; For E1 << E2:
;
;   If E1 is unsigned, the value of the result is E1 * 2^E2, reduced modulo one
;   more than the maximum representable value ni this type.
;
;   If E1 is signed and nonnegative, and if E1 * 2^E2 is representable, then it
;   is the resulting value.  Otherwise the behavior is undefined.
;
; For E1 >> E2:
;
;   If E1 is unsigned or signed and nonnegative, then the value is the integral
;   part of the uqotient E1 / 2^E2.
;
;   If E1 is signed and negative, the resulting value is implementation
;   defined.
;
; Per http://blog.llvm.org/2011/05/what-every-c-programmer-should-know.html,
; Clang and GCC accept -fwrapv, which requires signed integer overflow as
; defined except for dividing INT_MIN by -1.

; Wraparound with signed integer operations is apparently undefined in C.

; C standard 6.2.6.2 Integer Types
;  Unsigned integer types have value bits and padding bits (or no padding bits)
;  Signed integer types have value bits, padding bits, sign bit (maybe no padding bits)
;   Each value bit has the same value as the same bit in the corresponding unsigned type
;   Sign bit is zero means it doesn't affect the value
;   Sign bit is one can either be sign/magnitude, twos complement, or one complement
; Negative zeroes, if supported, can only be generated by certain operators, blah.
;   Behavior of &, |, etc., with operands that would produce negative zeroes, is undefined!
; Precision: width of the number not including sign bit
; Width: number of value bits plus the sign bit
;
; 6.3.1 Arithmetic Operands
;  integer conversion ranks
;  integer promotions
;    if the value can be represented by the new type, it is unchanged
;    else if the new type is unsigned, it is converted by repeatedly adding or subtracting
;       one more than the maximum value tha tcan be represented in the new type
;    else if the new type is signed, it is implementation defined
;
; so basically converting unsigneds that are too large into signed values is
; completely implementation defined.
;
; Maybe targeting C is a bad idea?
; Maybe we should target LLVM IR?

; http://llvm.org/docs/Frontend/PerformanceTips.html
;   add nsw/nuw flags as appropriate to help the optimizer
;   read "pass ordering" 

; http://llvm.org/docs/LangRef.html
;
; globals start with @ -- @foo, @bar, or unnamed @1, @2, ...
; locals begin with %  -- %foo, %bar, or unnamed %1, %2, ...
; semicolon comments
;
; module: contains functions, globals, and symbol table entries
;   can be fed to the linker
;   i don't see an explicit module keyword, maybe file is the scope
;
; globals (variables and functions) have linkage such as
;    private - accessible only to current module
;    internal - similar to private but somehow different, like "static" in C
;    ...
;    external - globally visible to the linker
;
; functions, calls, and invokes can specify their calling convention
;    ccc -- C calling convention for ABI compatibility
;    fastcc -- fast calling convention for code that doesnt' need to conform to the platform ABI
;    ... many other options ...
;
; "visibility style"-- somehow different than linkage
;
; thread_local variables 
;
; structure definitions:
;    %mytype = type { i32, i32, %mytype*, ... }
;
; global variables -- bunch of rules and stuff
;
; functions --
;  "define"  -- linkage, visibility, dll storage, calling convention, return type, blah blah...
;  "declare" -- all of that but no definition
;
; very interesting "named metadata" stuff could be used to provide debugging
; information like the original names of things in the source code
;
; parameter attributes:
; function return type, and function parameters, can have attributes
;  - zeroext: parameter/retval should be zero-extended if required by the ABI
;  - signext: parameter/retval should be sign-extended if required by the ABI
;  - inreg: compiler should use a register for this one
;  - byval: you should copy this pointer
;  - inalloca: for stack allocation
;  - sret: for first param only, for pointers only, indicates that this
;          param is a struct that is the return value: caller is then
;          responsible for alignment/etc. checking, making *this faster
;  - align <n>: optimizer may assume it is n-bit aligned
;  - noalias, nocapture, ...
;  - returned: this argument is returned, a tail recursion hint
;  - nonnull, ...

; function attributes
;   - inlinehint: you should probably inline this function
;   - alwaysinline: you should definitely inline this function
;   - noinline: you shuold never inline this ever
;   - cold: this is rarely called
;   - minsize: prefer small size over performance when optimizing this
;   - norecurse: this never calls itself directly or indirectly anywhere ever no way
;   - etc. lots of others, including stuff for saying that it is pure, reads no other memory, etc.

; type system
;  first class types can be produced by instructions
;    integers: iN for N up to 2^23 - 1
;      i5 - 5 bit integer; i32 32 bit integer, etc.
;
; LLVM uses 2's complement representation
;
; add: returns result modulo 2^n where n is the width of the result
;   add i32 %a, %b
;   add nuw i32 %a, %b  -- no unsigned wrap: result of the add is poison if unsigned overflow occurs
;   add nsw i32 %a, %b  -- no signed wrap: result of the add is poison if signed overflow occurs
;   add nuw nsw i32 %a, %b  -- result of the add is poison if signed or unsigned overflow occurs
;
; mul: happens to be the same (they say) for unsigned and signed because it's an
;    N bits * N bits -> lower N bits
;
; udiv versus sdiv: unsigned and signed divide, respectively
;     udiv by zero is undefined
;     sdiv by zero is undefined
;     sdiv of int_min by -1 is undefined
;  udiv is an integer quotient so it rounds towards 0
;  sdiv explicitly rounds towards 0, i.e., it should match truncate
;
; urem, srem, etc.





