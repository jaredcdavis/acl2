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
	%ans = icmp sle i64 %a, %b
	%ext = zext i1 %ans to i64
	ret i64 %ext
}

define i64 @narith_i64ult (i64 %a, i64 %b)
{
	%ans = icmp slt i64 %a, %b
	%ext = zext i1 %ans to i64
	ret i64 %ext
}

define i64 @narith_i64uge (i64 %a, i64 %b)
{
	%ans = icmp sge i64 %a, %b
	%ext = zext i1 %ans to i64
	ret i64 %ext
}

define i64 @narith_i64ugt (i64 %a, i64 %b)
{
	%ans = icmp sgt i64 %a, %b
	%ext = zext i1 %ans to i64
	ret i64 %ext
}


; Basic arithmetic ------------------------------------------------------------

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

define i64 @narith_i64plus (i64 %a, i64 %b)
{
       %ans = add i64 %a, %b
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

