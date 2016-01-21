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
(include-book "std/util/define" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable signed-byte-p)))

(defxdoc i64
  :parents (nativearith)
  :short "The signed integer type that all of our @(see operations) produce."
  :long "<p>We could just use @(see signed-byte-p) for this, but it seems
convenient for congruence reasoning, and just for less typing, to introduce our
own type.</p>")

(local (xdoc::set-default-parents i64))

(defsection i64-min
  :short "The minimum signed 64-bit value, @($-2^{63}$)."
  :long "@(def i64-min)"
  (defmacro i64-min ()
    (- (expt 2 63))))

(defsection i64-max
  :short "The maximum signed 64-bit value, @($2^{63} - 1$)."
  :long "@(def i64-max)"
  (defmacro i64-max ()
    (+ -1 (expt 2 63))))

(define i64-p (x)
  :short "Recognizer for signed, 64-bit integers."
  (signed-byte-p 64 x)
  ///
  (defthm i64-p-compound-recognizer
    (implies (i64-p x)
             (integerp x)))
  (defthm signed-byte-p-64-when-i64-p
    (implies (i64-p x)
             (signed-byte-p 64 x))))

(define i64-fix ((x i64-p))
  :short "Fixing function for signed, 64-bit integers."
  :returns (x-fix i64-p)
  :inline t
  (mbe :logic (logext 64 x)
       :exec x)
  :prepwork ((local (in-theory (enable i64-p))))
  ///
  (defthm i64-fix-when-i64-p
    (implies (i64-p x)
             (equal (i64-fix x)
                    x))))

(defsection i64-equiv
  :short "Equivalence relation for signed, 64-bit integers."
  (deffixtype i64
    :pred i64-p
    :fix i64-fix
    :equiv i64-equiv
    :define t
    :forward t
    :equal eql)

  (defrefinement int-equiv i64-equiv
    :hints(("Goal" :in-theory (enable i64-fix logext logapp loghead logbitp)))))


(deflist i64list
  :elt-type i64-p
  :true-listp t)

(define i64list-nth ((n natp)
                     (x i64list-p))
  :returns (nth i64-p)
  (mbe :logic (i64-fix (nth n x))
       :exec
       (or (case n
             (0 (first x))
             (1 (second x))
             (2 (third x))
             (otherwise (nth n x)))
           0))
  :prepwork
  ((local (include-book "arithmetic/top-with-meta" :dir :system))
   (local (include-book "std/lists/nth" :dir :system))
   (local (defthm l0
            (equal (< (+ c a) (+ c b))
                   (< a b))))

   (local (defthm |(< (+ -1 a) b)|
            (equal (< (+ -1 a) b)
                   (< a (+ 1 b)))
            :hints(("Goal"
                    :in-theory (disable l0)
                    :use ((:instance l0 (a (+ -1 a)) (b b) (c 1)))))))

   (local (defthm i64-p-of-nth-when-i64list-p
            (implies (i64list-p x)
                     (equal (i64-p (nth n x))
                            (< (nfix n) (len x))))))

   (local (defthm i64-fix-of-nth-when-i64list-p
            (implies (i64list-p x)
                     (equal (i64-fix (nth n x))
                            (if (< (nfix n) (len x))
                                (nth n x)
                              0)))))))

