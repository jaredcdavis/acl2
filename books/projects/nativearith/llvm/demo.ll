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

define i64 @narith_i64sdiv (i64 %a, i64 %b) noinline
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

define i64 @demo_circuit (i64* noalias nocapture align 8 %in,
                          i64* noalias nocapture align 8 %out)
{

; It appears that there's no reason to inline these address computations with
; the code that uses them.  LLVM will produce the same code either way.

    %in0.addr = getelementptr i64* %in, i32 0
    %in1.addr = getelementptr i64* %in, i32 1
    %in2.addr = getelementptr i64* %in, i32 2
    %in3.addr = getelementptr i64* %in, i32 3
    %in4.addr = getelementptr i64* %in, i32 4
    %in5.addr = getelementptr i64* %in, i32 5
    %in6.addr = getelementptr i64* %in, i32 6
    %in7.addr = getelementptr i64* %in, i32 7
    %in8.addr = getelementptr i64* %in, i32 8
    %in9.addr = getelementptr i64* %in, i32 9
    %in10.addr = getelementptr i64* %in, i32 10
    %in11.addr = getelementptr i64* %in, i32 11
    %in12.addr = getelementptr i64* %in, i32 12
    %in13.addr = getelementptr i64* %in, i32 13
    %in14.addr = getelementptr i64* %in, i32 14
    %in15.addr = getelementptr i64* %in, i32 15
    %in16.addr = getelementptr i64* %in, i32 16
    %in17.addr = getelementptr i64* %in, i32 17
    %in18.addr = getelementptr i64* %in, i32 18
    %in19.addr = getelementptr i64* %in, i32 19
    %in20.addr = getelementptr i64* %in, i32 20
    %in21.addr = getelementptr i64* %in, i32 21
    %in22.addr = getelementptr i64* %in, i32 22
    %in23.addr = getelementptr i64* %in, i32 23
    %in24.addr = getelementptr i64* %in, i32 24
    %in25.addr = getelementptr i64* %in, i32 25
    %in26.addr = getelementptr i64* %in, i32 26
    %in27.addr = getelementptr i64* %in, i32 27
    %in28.addr = getelementptr i64* %in, i32 28
    %in29.addr = getelementptr i64* %in, i32 29

    %out0.addr = getelementptr i64* %out, i32 0
    %out1.addr = getelementptr i64* %out, i32 1
    %out2.addr = getelementptr i64* %out, i32 2
    %out3.addr = getelementptr i64* %out, i32 3
    %out4.addr = getelementptr i64* %out, i32 4
    %out5.addr = getelementptr i64* %out, i32 5
    %out6.addr = getelementptr i64* %out, i32 6
    %out7.addr = getelementptr i64* %out, i32 7
    %out8.addr = getelementptr i64* %out, i32 8
    %out9.addr = getelementptr i64* %out, i32 9
    %out10.addr = getelementptr i64* %out, i32 10
    %out11.addr = getelementptr i64* %out, i32 11
    %out12.addr = getelementptr i64* %out, i32 12
    %out13.addr = getelementptr i64* %out, i32 13
    %out14.addr = getelementptr i64* %out, i32 14

; But this part is a bummer.  We get much better assembly when we interleave
; the loads/stores in with the operations.  This seems to hold on llvm 3.4 and
; 3.5, at least using opt with -O3.

    %in0 = load i64* %in0.addr, align 8
    %in1 = load i64* %in1.addr, align 8
    %ans0 = call i64 @narith_i64plus (i64 %in0, i64 %in1)
    store i64 %ans0, i64* %out0.addr, align 8, !nontemporal !{i32 1}

    %in2 = load i64* %in2.addr, align 8
    %in3 = load i64* %in3.addr, align 8
    %ans1 = call i64 @narith_i64plus (i64 %in2, i64 %in3)
    store i64 %ans1, i64* %out1.addr, align 8, !nontemporal !{i32 1}

    %in4 = load i64* %in4.addr, align 8
    %in5 = load i64* %in5.addr, align 8
    %ans2 = call i64 @narith_i64plus (i64 %in4, i64 %in5)
    store i64 %ans2, i64* %out2.addr, align 8, !nontemporal !{i32 1}

    %in6 = load i64* %in6.addr, align 8
    %in7 = load i64* %in7.addr, align 8
    %ans3 = call i64 @narith_i64plus (i64 %in6,i64 %in7)
    store i64 %ans3, i64* %out3.addr, align 8, !nontemporal !{i32 1}

    %in8 = load i64* %in8.addr, align 8
    %in9 = load i64* %in9.addr, align 8
    %ans4 = call i64 @narith_i64plus (i64 %in8, i64 %in9)
    store i64 %ans4, i64* %out4.addr, align 8, !nontemporal !{i32 1}

    %in10 = load i64* %in10.addr, align 8
    %in11 = load i64* %in11.addr, align 8
    %ans5 = call i64 @narith_i64plus (i64 %in10, i64 %in11)
    store i64 %ans5, i64* %out5.addr, align 8, !nontemporal !{i32 1}

    %in12 = load i64* %in12.addr, align 8
    %in13 = load i64* %in13.addr, align 8
    %ans6 = call i64 @narith_i64plus (i64 %in12, i64 %in13)
    store i64 %ans6, i64* %out6.addr, align 8, !nontemporal !{i32 1}

    %in14 = load i64* %in14.addr, align 8
    %in15 = load i64* %in15.addr, align 8
    %ans7 = call i64 @narith_i64plus (i64 %in14, i64 %in15)
    store i64 %ans7, i64* %out7.addr, align 8, !nontemporal !{i32 1}

    %in16 = load i64* %in16.addr, align 8
    %in17 = load i64* %in17.addr, align 8
    %ans8 = call i64 @narith_i64plus (i64 %in16, i64 %in17)
    store i64 %ans8, i64* %out8.addr, align 8, !nontemporal !{i32 1}

    %in18 = load i64* %in18.addr, align 8
    %in19 = load i64* %in19.addr, align 8
    %ans9 = call i64 @narith_i64plus (i64 %in18, i64 %in19)
    store i64 %ans9, i64* %out9.addr, align 8, !nontemporal !{i32 1}

    %in20 = load i64* %in20.addr, align 8
    %in21 = load i64* %in21.addr, align 8
    %ans10 = call i64 @narith_i64plus (i64 %in20, i64 %in21)
    store i64 %ans10, i64* %out10.addr, align 8, !nontemporal !{i32 1}

    %in22 = load i64* %in22.addr, align 8
    %in23 = load i64* %in23.addr, align 8
    %ans11 = call i64 @narith_i64plus (i64 %in22, i64 %in23)
    store i64 %ans11, i64* %out11.addr, align 8, !nontemporal !{i32 1}

    %in24 = load i64* %in24.addr, align 8
    %in25 = load i64* %in25.addr, align 8
    %ans12 = call i64 @narith_i64plus (i64 %in24, i64 %in25)
    store i64 %ans12, i64* %out12.addr, align 8, !nontemporal !{i32 1}

    %in26 = load i64* %in26.addr, align 8
    %in27 = load i64* %in27.addr, align 8
    %ans13 = call i64 @narith_i64plus (i64 %in26, i64 %in27)
    store i64 %ans13, i64* %out13.addr, align 8, !nontemporal !{i32 1}

    %in28 = load i64* %in28.addr, align 8
    %in29 = load i64* %in29.addr, align 8
    %ans14 = call i64 @narith_i64plus (i64 %in28, i64 %in29)
    store i64 %ans14, i64* %out14.addr, align 8, !nontemporal !{i32 1}

    ret i64 42
}






; So that's probably all we need for loads and stores.  But we may also
; want to implement something for branching.  As a particular example,
; consider a circuit that is to compute

;  w = sel1 ? a1 + b1
;    : sel2 ? a2 + b2
;    : sel3 ? a3 + b3
;    : a4 + b4

define i64 @narith_ite (i64 %cond, i64 %then, i64 %else)
{
    %cond.zero = icmp eq i64 %cond, 0
    br i1 %cond.zero, label %case.zero, label %case.nonzero

  case.nonzero:
    ret i64 %then

  case.zero:
    ret i64 %else
}

define i64 @demo_circuit2 (i64* noalias nocapture align 8 %in)
{
    %sel1.addr = getelementptr i64* %in, i32 0
    %sel2.addr = getelementptr i64* %in, i32 1
    %sel3.addr = getelementptr i64* %in, i32 2
    %a1.addr = getelementptr i64* %in, i32 3
    %a2.addr = getelementptr i64* %in, i32 4
    %a3.addr = getelementptr i64* %in, i32 5
    %a4.addr = getelementptr i64* %in, i32 6
    %b1.addr = getelementptr i64* %in, i32 7
    %b2.addr = getelementptr i64* %in, i32 8
    %b3.addr = getelementptr i64* %in, i32 9
    %b4.addr = getelementptr i64* %in, i32 10

    %a1 = load i64* %a1.addr, align 8
    %b1 = load i64* %b1.addr, align 8
    %sum1 = call i64 @narith_i64sdiv (i64 %a1, i64 %b1)

    %a2 = load i64* %a2.addr, align 8
    %b2 = load i64* %b2.addr, align 8
    %sum2 = call i64 @narith_i64sdiv (i64 %a2, i64 %b2)

    %a3 = load i64* %a3.addr, align 8
    %b3 = load i64* %b3.addr, align 8
    %sum3 = call i64 @narith_i64sdiv (i64 %a3, i64 %b3)

    %a4 = load i64* %a3.addr, align 8
    %b4 = load i64* %b3.addr, align 8
    %sum4 = call i64 @narith_i64sdiv (i64 %a4, i64 %b4)

    %sel1 = load i64* %sel1.addr, align 8
    %sel2 = load i64* %sel2.addr, align 8
    %sel3 = load i64* %sel3.addr, align 8
    %branch3 = call i64 @narith_ite (i64 %sel3, i64 %sum3, i64 %sum4)
    %branch2 = call i64 @narith_ite (i64 %sel2, i64 %sum2, i64 %branch3)
    %branch1 = call i64 @narith_ite (i64 %sel1, i64 %sum1, i64 %branch2)

    ret i64 %branch1
}


define i64 @demo_circuit2_alt1 (i64* noalias nocapture align 8 %in)
{
    %sel1.addr = getelementptr i64* %in, i32 0
    %sel2.addr = getelementptr i64* %in, i32 1
    %sel3.addr = getelementptr i64* %in, i32 2
    %a1.addr = getelementptr i64* %in, i32 3
    %a2.addr = getelementptr i64* %in, i32 4
    %a3.addr = getelementptr i64* %in, i32 5
    %a4.addr = getelementptr i64* %in, i32 6
    %b1.addr = getelementptr i64* %in, i32 7
    %b2.addr = getelementptr i64* %in, i32 8
    %b3.addr = getelementptr i64* %in, i32 9
    %b4.addr = getelementptr i64* %in, i32 10

    %sel1 = load i64* %sel1.addr, align 8
    %test1 = icmp ne i64 %sel1, 0
    br i1 %test1, label %case.case1, label %case.notcase1

  case.notcase1:

    %sel2 = load i64* %sel2.addr, align 8
    %test2 = icmp ne i64 %sel2, 0
    br i1 %test2, label %case.case2, label %case.notcase2

  case.notcase2:

    %sel3 = load i64* %sel3.addr, align 8
    %test3 = icmp ne i64 %sel3, 0
    br i1 %test3, label %case.case3, label %case.notcase3

  case.notcase3:

    %a4 = load i64* %a3.addr, align 8
    %b4 = load i64* %b3.addr, align 8
    %sum4 = call i64 @narith_i64plus (i64 %a4, i64 %b4)
    ret i64 %sum4

  case.case1:

    %a1 = load i64* %a1.addr, align 8
    %b1 = load i64* %b1.addr, align 8
    %sum1 = call i64 @narith_i64plus (i64 %a1, i64 %b1)
    ret i64 %sum1

  case.case2:

    %a2 = load i64* %a2.addr, align 8
    %b2 = load i64* %b2.addr, align 8
    %sum2 = call i64 @narith_i64plus (i64 %a2, i64 %b2)
    ret i64 %sum2

  case.case3:

    %a3 = load i64* %a3.addr, align 8
    %b3 = load i64* %b3.addr, align 8
    %sum3 = call i64 @narith_i64plus (i64 %a3, i64 %b3)
    ret i64 %sum3
}


; This is the same sort of manual idea, but it avoids the multiple return
; and instead has a reconvergence to the "finish" label, using a phi node.

define i64 @demo_circuit2_alt2 (i64* noalias nocapture align 8 %in)
{
    %sel1.addr = getelementptr i64* %in, i32 0
    %sel2.addr = getelementptr i64* %in, i32 1
    %sel3.addr = getelementptr i64* %in, i32 2
    %a1.addr = getelementptr i64* %in, i32 3
    %a2.addr = getelementptr i64* %in, i32 4
    %a3.addr = getelementptr i64* %in, i32 5
    %a4.addr = getelementptr i64* %in, i32 6
    %b1.addr = getelementptr i64* %in, i32 7
    %b2.addr = getelementptr i64* %in, i32 8
    %b3.addr = getelementptr i64* %in, i32 9
    %b4.addr = getelementptr i64* %in, i32 10

    %sel1 = load i64* %sel1.addr, align 8
    %test1 = icmp ne i64 %sel1, 0
    br i1 %test1, label %case.case1, label %case.notcase1

  case.notcase1:

    %sel2 = load i64* %sel2.addr, align 8
    %test2 = icmp ne i64 %sel2, 0
    br i1 %test2, label %case.case2, label %case.notcase2

  case.notcase2:

    %sel3 = load i64* %sel3.addr, align 8
    %test3 = icmp ne i64 %sel3, 0
    br i1 %test3, label %case.case3, label %case.notcase3

  case.notcase3:

    %a4 = load i64* %a3.addr, align 8
    %b4 = load i64* %b3.addr, align 8
    %sum4 = call i64 @narith_i64plus (i64 %a4, i64 %b4)
    br label %finish

  case.case1:

    %a1 = load i64* %a1.addr, align 8
    %b1 = load i64* %b1.addr, align 8
    %sum1 = call i64 @narith_i64plus (i64 %a1, i64 %b1)
    br label %finish

  case.case2:

    %a2 = load i64* %a2.addr, align 8
    %b2 = load i64* %b2.addr, align 8
    %sum2 = call i64 @narith_i64plus (i64 %a2, i64 %b2)
    br label %finish

  case.case3:

    %a3 = load i64* %a3.addr, align 8
    %b3 = load i64* %b3.addr, align 8
    %sum3 = call i64 @narith_i64plus (i64 %a3, i64 %b3)
    br label %finish

  finish:
    %ret = phi i64 [%sum1, %case.case1],
                   [%sum2, %case.case2],
                   [%sum3, %case.case3],
                   [%sum4, %case.notcase3]
    ret i64 %ret
}



; We now take advantage of reconvergence to do something with the
; answer W after we compute it.  In particular we do:

;  w = sel1 ? a1 + b1
;    : sel2 ? a2 + b2
;    : sel3 ? a3 + b3
;    : a4 + b4
;
;  return (w + a5) * 2

define i64 @demo_circuit3 (i64* noalias nocapture align 8 %in)
{
    %sel1.addr = getelementptr i64* %in, i32 0
    %sel2.addr = getelementptr i64* %in, i32 1
    %sel3.addr = getelementptr i64* %in, i32 2
    %a1.addr = getelementptr i64* %in, i32 3
    %a2.addr = getelementptr i64* %in, i32 4
    %a3.addr = getelementptr i64* %in, i32 5
    %a4.addr = getelementptr i64* %in, i32 6
    %b1.addr = getelementptr i64* %in, i32 7
    %b2.addr = getelementptr i64* %in, i32 8
    %b3.addr = getelementptr i64* %in, i32 9
    %b4.addr = getelementptr i64* %in, i32 10
    %a5.addr = getelementptr i64* %in, i32 11


    %sel1 = load i64* %sel1.addr, align 8
    %test1 = icmp ne i64 %sel1, 0
    br i1 %test1, label %case.case1, label %case.notcase1

  case.notcase1:

    %sel2 = load i64* %sel2.addr, align 8
    %test2 = icmp ne i64 %sel2, 0
    br i1 %test2, label %case.case2, label %case.notcase2

  case.notcase2:

    %sel3 = load i64* %sel3.addr, align 8
    %test3 = icmp ne i64 %sel3, 0
    br i1 %test3, label %case.case3, label %case.notcase3

  case.notcase3:

    %a4 = load i64* %a3.addr, align 8
    %b4 = load i64* %b3.addr, align 8
    %sum4 = call i64 @narith_i64plus (i64 %a4, i64 %b4)
    br label %finish

  case.case1:

    %a1 = load i64* %a1.addr, align 8
    %b1 = load i64* %b1.addr, align 8
    %sum1 = call i64 @narith_i64plus (i64 %a1, i64 %b1)
    br label %finish

  case.case2:

    %a2 = load i64* %a2.addr, align 8
    %b2 = load i64* %b2.addr, align 8
    %sum2 = call i64 @narith_i64plus (i64 %a2, i64 %b2)
    br label %finish

  case.case3:

    %a3 = load i64* %a3.addr, align 8
    %b3 = load i64* %b3.addr, align 8
    %sum3 = call i64 @narith_i64plus (i64 %a3, i64 %b3)
    br label %finish

  finish:
    %w = phi i64 [%sum1, %case.case1],
                   [%sum2, %case.case2],
                   [%sum3, %case.case3],
                   [%sum4, %case.notcase3]

    %a5 = load i64* %a5.addr, align 8
    %tmp1 = call i64 @narith_i64plus(i64 %w, i64 %a5)

;    %two = add i64 0, 2

    %ret = call i64 @narith_i64times(i64 %tmp1, i64 2)

    ret i64 %ret
}



; So what is this really?
;
;  w = sel1 ? a1 + b1
;    : sel2 ? a2 + b2
;    : sel3 ? a3 + b3
;    : a4 + b4
;
;  return (w + a5) * 2
;
;
; It's really something like:
;
;   n1 = a1 + b1;
;   n2 = a2 + b2;
;   n3 = a3 + b3;
;   n4 = a4 + b4;
;   n5 = sel3 ? n3 : n4;
;   n6 = sel2 ? n2 : n5;
;   w = sel1 ? n1 : n6;
;   n8 = w + a5;
;   ret = n8 * 2;
;
; Let's change this so that instead of a3 + b3, the sel3 case returns a1 + b1.
; That is,
;
;  w = sel1 ? a1 + b1
;    : sel2 ? a2 + b2
;    : sel3 ? a1 + b1
;    : a4 + b4
;
;  return (w + a5) * 2
;
; In other words:
;
;   n1 = a1 + b1;
;   n2 = a2 + b2;
;                                ; n3 goes away
;   n4 = a4 + b4;
;   n5 = sel3 ? n1 : n4;
;   n6 = sel2 ? n2 : n5;
;   w = sel1 ? n1 : n6;
;   n8 = w + a5;
;   ret = n8 * 2;
;
; Now can we get a nice jumping structure that computes n1 exactly when it is needed?
;
; Let's change it even more, to:

;  w = sel1 ? a1 * b1
;    : sel2 ? a2 + b2
;    : sel3 ? a1 * b1
;    : a4 + b4
;
;  return (w + a5) + 2
;
; In other words:
;
;   n1 = a1 * b1;
;   n2 = a2 + b2;
;   n4 = a4 + b4;
;   n5 = sel3 ? n1 : n4;
;   n6 = sel2 ? n2 : n5;
;   w = sel1 ? n1 : n6;
;   n8 = w + a5;
;   ret = n8 + 2;
;
; And we want to get a program with just one multiply.
; So this works to get just one multiply, but it does it in the prelude before
; any of the branches:


define i64 @demo_circuit4 (i64* noalias nocapture align 8 %in)
{
    %sel1.addr = getelementptr i64* %in, i32 0
    %sel2.addr = getelementptr i64* %in, i32 1
    %sel3.addr = getelementptr i64* %in, i32 2
    %a1.addr = getelementptr i64* %in, i32 3
    %a2.addr = getelementptr i64* %in, i32 4
    %a3.addr = getelementptr i64* %in, i32 5
    %a4.addr = getelementptr i64* %in, i32 6
    %a5.addr = getelementptr i64* %in, i32 7
    %b1.addr = getelementptr i64* %in, i32 8
    %b2.addr = getelementptr i64* %in, i32 9
    %b3.addr = getelementptr i64* %in, i32 10
    %b4.addr = getelementptr i64* %in, i32 11

    %a1 = load i64* %a1.addr, align 8
    %b1 = load i64* %b1.addr, align 8
    %n1 = call i64 @narith_i64times (i64 %a1, i64 %b1)

    %a2 = load i64* %a2.addr, align 8
    %b2 = load i64* %b2.addr, align 8
    %n2 = call i64 @narith_i64plus (i64 %a2, i64 %b2)

    %a4 = load i64* %a3.addr, align 8
    %b4 = load i64* %b3.addr, align 8
    %n4 = call i64 @narith_i64plus (i64 %a4, i64 %b4)

    %sel1 = load i64* %sel1.addr, align 8
    %sel2 = load i64* %sel2.addr, align 8
    %sel3 = load i64* %sel3.addr, align 8
    %n5 = call i64 @narith_ite (i64 %sel3, i64 %n1, i64 %n4)
    %n6 = call i64 @narith_ite (i64 %sel2, i64 %n2, i64 %n5)
    %w = call i64 @narith_ite (i64 %sel1, i64 %n1, i64 %n6)

    %a5 = load i64* %a5.addr, align 8
    %n8 = call i64 @narith_i64plus(i64 %w, i64 %a5)
    %ret = call i64 @narith_i64plus(i64 %n8, i64 2)

    ret i64 %ret
}

; define i64 @demo_circuit4b (i64* noalias nocapture align 8 %in)
; {
;     %sel1.addr = getelementptr i64* %in, i32 0
;     %sel2.addr = getelementptr i64* %in, i32 1
;     %sel3.addr = getelementptr i64* %in, i32 2
;     %a1.addr = getelementptr i64* %in, i32 3
;     %a2.addr = getelementptr i64* %in, i32 4
;     %a3.addr = getelementptr i64* %in, i32 5
;     %a4.addr = getelementptr i64* %in, i32 6
;     %a5.addr = getelementptr i64* %in, i32 7
;     %b1.addr = getelementptr i64* %in, i32 8
;     %b2.addr = getelementptr i64* %in, i32 9
;     %b3.addr = getelementptr i64* %in, i32 10
;     %b4.addr = getelementptr i64* %in, i32 11

;     %sel1 = load i64* %sel1.addr, align 8
;     %test1 = icmp ne i64 %sel1, 0
;     br i1 %test1, label %case.case1, label %case.notcase1



;     %sel2 = load i64* %sel2.addr, align 8
;     %sel3 = load i64* %sel3.addr, align 8


;     %a1 = load i64* %a1.addr, align 8
;     %b1 = load i64* %b1.addr, align 8
;     %n1 = call i64 @narith_i64times (i64 %a1, i64 %b1)

;     %a2 = load i64* %a2.addr, align 8
;     %b2 = load i64* %b2.addr, align 8
;     %n2 = call i64 @narith_i64plus (i64 %a2, i64 %b2)

;     %a4 = load i64* %a3.addr, align 8
;     %b4 = load i64* %b3.addr, align 8
;     %n4 = call i64 @narith_i64plus (i64 %a4, i64 %b4)

;     %n5 = call i64 @narith_ite (i64 %sel3, i64 %n1, i64 %n4)
;     %n6 = call i64 @narith_ite (i64 %sel2, i64 %n2, i64 %n5)
;     %w = call i64 @narith_ite (i64 %sel1, i64 %n1, i64 %n6)

;     %a5 = load i64* %a5.addr, align 8
;     %n8 = call i64 @narith_i64plus(i64 %w, i64 %a5)
;     %ret = call i64 @narith_i64plus(i64 %n8, i64 2)

;     ret i64 %ret
; }


