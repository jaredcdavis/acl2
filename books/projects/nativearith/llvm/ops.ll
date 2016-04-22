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

; Equality comparisons --------------------------------------------------------

define i64 @narith_i64eql (i64 %a, i64 %b)
{
    %ans = icmp eq i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}

define i64 @narith_i64neq (i64 %a, i64 %b)
{
    %ans = icmp ne i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}


; Signed comparisons ----------------------------------------------------------

define i64 @narith_i64sle (i64 %a, i64 %b)
{
    %ans = icmp sle i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}

define i64 @narith_i64slt (i64 %a, i64 %b)
{
    %ans = icmp slt i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}

define i64 @narith_i64sge (i64 %a, i64 %b)
{
    %ans = icmp sge i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}

define i64 @narith_i64sgt (i64 %a, i64 %b)
{
    %ans = icmp sgt i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}


; Unsigned comparisons --------------------------------------------------------

define i64 @narith_i64ule (i64 %a, i64 %b)
{
    %ans = icmp ule i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}

define i64 @narith_i64ult (i64 %a, i64 %b)
{
    %ans = icmp ult i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}

define i64 @narith_i64uge (i64 %a, i64 %b)
{
    %ans = icmp uge i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}

define i64 @narith_i64ugt (i64 %a, i64 %b)
{
    %ans = icmp ugt i64 %a, %b
    %ext = zext i1 %ans to i64
    ret i64 %ext
}


; Basic arithmetic ------------------------------------------------------------

define i64 @narith_i64bitnot (i64 %a)
{
    %ans = xor i64 %a, -1
    ret i64 %ans
}

define i64 @narith_i64sminus (i64 %a)
{
    %ans = sub i64 0, %a
    ret i64 %ans
}

define i64 @narith_i64logcar (i64 %a)
{
    %ans = and i64 1, %a
    ret i64 %ans
}

define i64 @narith_i64logcdr (i64 %a)
{
    %ans = ashr i64 %a, 1
    ret i64 %ans
}

define i64 @narith_i64bitand (i64 %a, i64 %b)
{
    %ans = and i64 %a, %b
    ret i64 %ans
}

define i64 @narith_i64bitor (i64 %a, i64 %b)
{
    %ans = or i64 %a, %b
    ret i64 %ans
}

define i64 @narith_i64bitxor (i64 %a, i64 %b)
{
    %ans = xor i64 %a, %b
    ret i64 %ans
}

define i64 @narith_i64loghead (i64 %a, i64 %b)
{
    ;; Since this is a variable width loghead, I don't think we can use the
    ;; LLVM zext operation because that extends one type to another.  Instead,
    ;; the simplest way I see to do this is shift left then right (logical) to
    ;; clear out the high bits.
    ;;
    ;; Three cases to consider.
    ;;   Toosmall case. (loghead a b) where A <= 0.   We must return 0.
    ;;   Toobig case.   (loghead a b) where A >= 64.  We must return B.
    ;;   Usual case.    (loghead a b) otherwise.      We need to zero part of B.
    ;;
    ;; As an example of the usual case, suppose A is 5.  Then we want to keep
    ;; only the low 5 bits of B.  Since B is 64 bits, we want to shift left and
    ;; then right by 64 - A bits.  That is, we should do:
    ;;
    ;;      ((B << 59) >> 59)
    ;;
    ;; Because 64 - 5 == 59 bits.
    ;;
    ;; Does this shifting approach happen to work out for the toobig and/or
    ;; toosmall cases?  Unfortunately no.  Per the LLVM manual, the shift
    ;; instructions treat the shift amount as an unsigned value, and if the
    ;; shift amount is larger than the width of B, the result is undefined.
    ;; So, we have to have explicit bounds checks here.
    %a.toobig = icmp sgt i64 %a, 64
    br i1 %a.toobig, label %case.toobig, label %case.nottoobig
  case.toobig:
    ret i64 %b
  case.nottoobig:
    %a.toosmall = icmp sle i64 %a, 0
    br i1 %a.toosmall, label %case.toosmall, label %case.normal
  case.toosmall:
    ret i64 0
  case.normal:
    %amt = sub i64 64, %a
    %tmp = shl i64 %b, %amt
    %ans = lshr i64 %tmp, %amt
    ret i64 %ans
}

define i64 @narith_i64logext (i64 %a, i64 %b)
{
    ;; Basically similar to loghead.
    %a.toobig = icmp sgt i64 %a, 64
    br i1 %a.toobig, label %case.toobig, label %case.nottoobig
  case.toobig:
    ret i64 %b
  case.nottoobig:
    %a.toosmall = icmp sle i64 %a, 0
    br i1 %a.toosmall, label %case.toosmall, label %case.normal
  case.toosmall:
    %lsb = trunc i64 %b to i1
    %ext = sext i1 %lsb to i64
    ret i64 %ext
  case.normal:
    %amt = sub i64 64, %a
    %tmp = shl i64 %b, %amt
    %ans = ashr i64 %tmp, %amt
    ret i64 %ans
}

define i64 @narith_i64shl (i64 %a, i64 %b)
{
    ;; Similar to loghead, we need an explicit bounds check on the shift
    ;; amount.  We can use an unsigned bounds check since our shl operation
    ;; interprets b as unsigned.
    %b.toobig = icmp uge i64 %b, 64
    br i1 %b.toobig, label %case.toobig, label %case.nottoobig
  case.toobig:
    ret i64 0
  case.nottoobig:
    %ans = shl i64 %a, %b
    ret i64 %ans
}

define i64 @narith_i64plus (i64 %a, i64 %b)
{
       %ans = add i64 %a, %b
       ret i64 %ans
}

declare {i64, i1} @llvm.uadd.with.overflow.i64(i64 %a, i64 %b)

define i64 @narith_i64upluscarry (i64 %a, i64 %b)
{
    ;; BOZO I don't know if this is a very good way to implement this
    ;; operation, but it is simple and seems likely to be something that
    ;; LLVM is designed to optimize.  It would probably be good to
    ;; eventually consider other approaches, but for now I just want to
    ;; get something working.
    %res = call {i64, i1} @llvm.uadd.with.overflow.i64(i64 %a, i64 %b)
    %carry = extractvalue {i64, i1} %res, 1
    %ans = zext i1 %carry to i64
    ret i64 %ans
}

define i64 @narith_i64minus (i64 %a, i64 %b)
{
    %ans = sub i64 %a, %b
    ret i64 %ans
}

define i64 @narith_i64times (i64 %a, i64 %b)
{
    %ans = mul i64 %a, %b
    ret i64 %ans
}


; Division --------------------------------------------------------------------

define i64 @narith_i64sdiv (i64 %a, i64 %b)
{
    %b.zero = icmp eq i64 %b, 0
    br i1 %b.zero, label %case.zero, label %case.nonzero

  case.nonzero:
    %a.intmin = icmp eq i64 %a, -9223372036854775808
    %b.minus1 = icmp eq i64 %b, -1
    %overflow = and i1 %a.intmin, %b.minus1
    br i1 %overflow, label %case.overflow, label %case.usual

  case.zero:
    ret i64 0

  case.overflow:
    ret i64 %a

  case.usual:
    %ans = sdiv i64 %a, %b
    ret i64 %ans
}

define i64 @narith_i64udiv (i64 %a, i64 %b)
{
    %b.zero = icmp eq i64 %b, 0
    br i1 %b.zero, label %case.zero, label %case.nonzero

  case.nonzero:
    %ans = udiv i64 %a, %b
    ret i64 %ans

  case.zero:
    ret i64 0
}

