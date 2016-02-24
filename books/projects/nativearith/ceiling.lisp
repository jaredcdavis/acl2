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
(local (include-book "arithmetic/top" :dir :system))

; ceiling.lisp
;
; This is a basic book about the "ceiling" function.
;
; Credit belongs, I believe, to Ruben Gamboa, whose proofs of the basic
; bounding theorems in nonstd/nsa/sqrt.lisp I have adapted and put here.

(local (defthm ceiling-greater-than-quotient-aux
         (implies (and (integerp i)
                       (integerp j)
                       (< 0 j))
                  (< (/ i j) (1+ (nonnegative-integer-quotient i j))))
         :rule-classes (:linear :rewrite)))

(defthm ceiling-greater-than-quotient
  (implies (and (rationalp x)
                (rationalp y)
                (<= 0 x)
                (< 0 y))
           (<= (/ x y) (ceiling x y)))
  :rule-classes (:linear :rewrite)
  :hints (("Goal"
           :in-theory (disable ceiling-greater-than-quotient-aux)
           :use (:instance ceiling-greater-than-quotient-aux
                 (i (numerator (* x (/ y))))
                 (j (denominator (* x (/ y))))))))

(defthm lower-bound-of-remultiply-ceiling
  (implies (and (rationalp y)
                (rationalp x)
                (< 0 x)
                (< 0 y))
           (<= x (* y (ceiling x y))))
  :rule-classes :linear
  :hints(("Goal"
          :in-theory (disable ceiling-greater-than-quotient)
          :use ((:instance ceiling-greater-than-quotient)))))

(defthm ceiling-of-zero-left
  (equal (ceiling 0 a)
         0))

(defthm ceiling-of-zero-right
  (equal (ceiling a 0)
         0))

(defthm natp-of-ceiling
  (implies (and (rationalp a)
                (<= 0 a)
                (<= 0 b))
           (natp (ceiling a b)))
  :rule-classes :type-prescription)

(defthm posp-of-ceiling
  (implies (and (rationalp a)
                (rationalp b)
                (< 0 a)
                (< 0 b))
           (posp (ceiling a b)))
  :rule-classes :type-prescription)

(in-theory (disable ceiling))

