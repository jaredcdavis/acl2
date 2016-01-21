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
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
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
     (mbe :logic
          (b* ((a (,fix 64 a))
               (b (,fix 64 b)))
            ,logic)
          :exec
          ,exec)
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

(def-i64-arith2 i64plus
  :short "64-bit integer addition, i.e., @('a + b')."
  :long "<p>Note that this produces the same answer whether @('a') and @('b')
         are interpreted as signed or unsigned.</p>"
  :inline nil
  :logic (logext 64 (+ a b))
  :exec (fast-logext 64 (+ a b)))

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





