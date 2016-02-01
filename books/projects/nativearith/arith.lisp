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
(include-book "ihs/basic-definitions" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/fty/fixequiv" :dir :system))
(local (include-book "tools/do-not" :dir :system))
(local (acl2::do-not generalize fertilize))
(local (in-theory (disable signed-byte-p unsigned-byte-p acl2::zip-open)))
(local (std::add-default-post-define-hook :fix))

(defthm signed-byte-p-when-bitp
  (implies (and (syntaxp (quotep n))
                (natp n)
                (<= 2 n)
                (bitp x))
           (signed-byte-p n x))
  :hints(("Goal" :in-theory (enable bitp))))


(defrule zip-of-logcons
  (equal (zip (logcons a x))
         (and (not (eql a 1))
              (zip x)))
  :hints(("Goal" :in-theory (enable acl2::zip-open))))

(defruled logapp-redef
  (equal (logapp n a b)
         (logior (ash b (nfix n))
                 (loghead n a)))
  :enable (ihsext-recursive-redefs
           ihsext-inductions))

(defrule equal-of-logapp-split
  (implies (integerp x)
           (equal (equal (logapp n a b) x)
                  (and (equal (loghead n a)
                              (loghead n x))
                       (equal (ifix b) (ash x (- (nfix n)))))))
  :enable (ihsext-recursive-redefs ihsext-inductions)
  :disable (signed-byte-p))

(defrule equal-of-loghead-ns-when-signed-byte-p-ns
  (implies (and (signed-byte-p n x)
                (signed-byte-p n y))
           (equal (equal (loghead n x) (loghead n y))
                  (equal x y)))
  :disable (signed-byte-p)
  :enable (ihsext-inductions
           ihsext-recursive-redefs))

(defrule equal-loghead-0-when-signed-byte-p
  (implies (signed-byte-p n x)
           (equal (equal (loghead n x) 0)
                  (equal x 0)))
  :enable (ihsext-recursive-redefs
           ihsext-inductions)
  :disable (signed-byte-p))

(encapsulate
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
      :use ((:instance l0 (n 64))))))

(defrule logtail-n-when-signed-byte-p-n
  (implies (signed-byte-p n x)
           (equal (logtail n x)
                  (if (< x 0)
                      -1
                    0)))
  :disable (signed-byte-p)
  :enable (ihsext-recursive-redefs ihsext-inductions))

(defrule logapp-of-logext-same
  (equal (logapp n (logext n x) y)
         (logapp n x y)))

(defrule equal-of-expanded-logapp
  (implies (natp n)
           (equal (equal (logior (ash b1 n) (loghead n a1))
                         (logior (ash b2 n) (loghead n a2)))
                  (and (equal (loghead n a1)
                              (loghead n a2))
                       (equal (ifix b1)
                              (ifix b2)))))
  :enable (ihsext-recursive-redefs
           ihsext-inductions)
  ;; Just a dumb accumulated-persistence speed hint
  :disable (acl2::loghead-identity
            unsigned-byte-p**
            signed-byte-p**
            EQUAL-LOGHEAD-0-WHEN-SIGNED-BYTE-P
            bitops::signed-byte-p-of-logcdr
            bitops::logcdr-natp
            bitops::ash-natp-type
            acl2::unsigned-byte-p-plus))

(defrule equal-of-same-size-logapps
  (equal (equal (logapp 64 a1 b1)
                (logapp 64 a2 b2))
         (and (equal (loghead 64 a1)
                     (loghead 64 a2))
              (equal (ifix b1) (ifix b2))))
  :enable logapp-redef)

(defrule equal-of-shift-left-and-zero
  (implies (natp n)
           (equal (equal (ash b n) 0)
                  (equal (ifix b) 0)))
  :enable (ihsext-recursive-redefs
           ihsext-inductions))

(defrule equal-of-logapp-and-zero
  (equal (equal (logapp n a b) 0)
         (and (equal (loghead n a) 0)
              (equal (ifix b) 0)))
  :enable logapp-redef)

(defrule equal-of-logapp-and-minus1
  (equal (equal (logapp n a b) -1)
         (and (equal (ifix b) -1)
              (equal (loghead n a) (loghead n -1))))
  :enable (ihsext-recursive-redefs
           ihsext-inductions))

(defrule logapp-of-loghead-and-logtail
  (equal (logapp n (loghead n x) (logtail n x))
         (ifix x))
  :enable (ihsext-inductions
           ihsext-recursive-redefs))

(defrule <-of-logapps
  (equal (< (logapp n a1 b1)
            (logapp n a2 b2))
         (if (< (ifix b1) (ifix b2))
             t
           (and (equal (ifix b1) (ifix b2))
                (< (loghead n a1)
                   (loghead n a2)))))
  :enable (ihsext-recursive-redefs
           ihsext-inductions))

(defrule <-of-logapp-split
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
         (b2 (logtail n x)))))

(defrule <-of-logapp-split-right
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
         (b2 b))))


(local (defrule logcar-when-not-integerp
         (implies (not (integerp a))
                  (equal (logcar a) 0))
         :enable logcar))

(local (defrule logcdr-when-not-integerp
         (implies (not (integerp a))
                  (equal (logcdr a) 0))
         :enable logcdr))


(define recursive-plus-base-case ((cin bitp)
                                  (a   integerp)
                                  (b   integerp))
  :guard (and (or (eql a -1) (eql a 0))
              (or (eql b -1) (eql b 0)))
  :returns sum
  :short "Computes @('A + B + Cin') where A,B are -1 or 0, and Cin is a bit."
  :long "<p>This is pretty weird but I'm not sure if there's a better way to
         write it.</p>
         @({
                  A    B    CIN      Sum
                --------------------------
                  0    0    0        0
                  0    0    1        1
                  0   -1    0        -1
                  0   -1    1        0
                 -1    0    0        -1
                 -1    0    1        0
                 -1   -1    0        -2
                 -1   -1    1        -1
         })"
  :inline t
  :verify-guards nil
  (mbe :logic
       (let ((a0 (logcar a))
             (b0 (logcar b)))
         (logcons (b-xor cin (b-xor a0 b0))
                  (logext 1 (b-ior (b-and a0 b0)
                                   (b-and (b-xor a0 b0)
                                          (b-not cin))))))
       :exec
       (the (signed-byte 2)
            (+ (the bit cin)
               (the (signed-byte 2)
                    (+ (the (signed-byte 1) a)
                       (the (signed-byte 1) b))))))
  ///

  "<p>Since this is generally intended for reasoning about @('+') in a
   recursive way, the correctness theorem is disabled by default so that you
   can avoid introducing @('+') terms.</p>"

  (defruled recursive-plus-base-case-correct
    (implies (and (or (zip a) (eql a -1))
                  (or (zip b) (eql b -1)))
             (equal (recursive-plus-base-case cin a b)
                    (+ (bfix cin) (ifix a) (ifix b))))
    ;; Just let things open up and prove it by cases.
    :enable (bfix b-not b-xor b-and bitp zip logcar))

  (defrule logcar-of-recursive-plus-base-case
    (equal (logcar (recursive-plus-base-case cin a b))
           (b-xor cin (b-xor (logcar a) (logcar b)))))

  (defrule recursive-plus-baze-case-of-zeroes
    (equal (recursive-plus-base-case cin 0 0)
           (bfix cin)))

  (verify-guards recursive-plus-base-case$inline
    :hints(("Goal" :use ((:instance recursive-plus-base-case-correct))))))


(define recursive-plus ((cin bitp)
                        (a   integerp)
                        (b   integerp))
  :returns sum
  :measure (+ (integer-length a) (integer-length b))
  :hints(("Goal" :in-theory (enable* integer-length**)))
  :inline t
  :verify-guards nil
  :verbosep t
  (mbe :logic
       (b* (((when (and (or (zip a) (eql a -1))
                        (or (zip b) (eql b -1))))
             (recursive-plus-base-case cin a b))
            ;; Inductive case: standard ripple carry adder
            (a0   (logcar a))
            (b0   (logcar b))
            (sum  (b-xor cin (b-xor a0 b0)))
            (cout (b-ior (b-and a0 b0)
                         (b-and cin (b-ior a0 b0)))))
         (logcons sum
                  (recursive-plus cout (logcdr a) (logcdr b))))
       :exec
       (+ cin a b))
  ///
  (acl2::add-to-ruleset ihsext-inductions '((:i recursive-plus)))
  (acl2::add-to-ruleset ihsext-recursive-redefs '((:d recursive-plus)))

  (local (defruled inductive-step
           (let* ((a0   (logcar a))
                  (b0   (logcar b))
                  (sum  (b-xor cin (b-xor a0 b0)))
                  (cout (b-ior (b-and a0 b0)
                               (b-and cin (b-ior a0 b0))))
                  (rest (+ cout (logcdr a) (logcdr b))))
             (equal (logcons sum rest)
                    (+ (bfix cin) (ifix a) (ifix b))))
           :enable (b-ior b-and b-xor b-not)
           :disable (bitops::+-of-logcons-with-cin)
           :use ((:instance bitops::+-of-logcons-with-cin
                  (cin (bfix cin))
                  (b1 (logcar a))
                  (r1 (logcdr a))
                  (b2 (logcar b))
                  (r2 (logcdr b))))))

  (defruled recursive-plus-correct
    (equal (recursive-plus cin a b)
           (+ (bfix cin) (ifix a) (ifix b)))
    :hints(("Goal"
            :induct (recursive-plus cin a b)
            :in-theory (enable recursive-plus-base-case-correct))
           ;; Baaaah, can't get rid of it!
           ("Subgoal *1/2" :use ((:instance inductive-step)))))

  (verify-guards recursive-plus$inline
    :hints(("Goal" :use ((:instance recursive-plus-correct)))))

  (defrule recursive-plus-of-zeroes
    (and (equal (recursive-plus cin 0 0)
                (bfix cin))
         (equal (recursive-plus 0 a 0)
                (ifix a))
         (equal (recursive-plus 0 0 b)
                (ifix b)))
    :enable (recursive-plus-correct)
    :disable (recursive-plus)))

(define plus-ucarryout-n ((n natp)
                          (cin bitp)
                          (a integerp)
                          (b integerp))
  :returns (cout bitp)
  :measure (nfix n)
  (b* (((when (zp n))
        (bfix cin))
       (a0   (logcar a))
       (b0   (logcar b))
       (cout (b-ior (b-and a0 b0)
                    (b-and cin (b-ior a0 b0)))))
    (plus-ucarryout-n (- n 1) cout (logcdr a) (logcdr b)))
  ///
  (acl2::add-to-ruleset ihsext-recursive-redefs '((:d plus-ucarryout-n)))
  (acl2::add-to-ruleset ihsext-inductions '((:i plus-ucarryout-n)))

  (defrule plus-ucarryout-n-of-loghead-n-a
    (equal (plus-ucarryout-n n cin (loghead n a) b)
           (plus-ucarryout-n n cin a b))
    :enable (ihsext-recursive-redefs))

  (defrule plus-ucarryout-n-of-loghead-n-b
    (equal (plus-ucarryout-n n cin a (loghead n b))
           (plus-ucarryout-n n cin a b))
    :enable (ihsext-recursive-redefs))

  (defruled plus-ucarryout-n-as-unsigned-byte-p
    (implies (and (unsigned-byte-p n a)
                  (unsigned-byte-p n b)
                  (bitp cin))
             (equal (plus-ucarryout-n n cin a b)
                    (bool->bit (not (unsigned-byte-p n (recursive-plus cin a b))))))
    :hints(("Goal"
            :induct (plus-ucarryout-n n cin a b)
            :in-theory (enable* ihsext-recursive-redefs
                                recursive-plus
                                recursive-plus-base-case
                                b-not))))

  (defrule plus-ucarryout-n-special-cases
    (and (equal (plus-ucarryout-n n 0 0 b) 0)
         (equal (plus-ucarryout-n n 0 a 0) 0)))

  (defrule plus-ucarryout-n-of-logext-n-a
    (equal (plus-ucarryout-n n cin (logext n a) b)
           (plus-ucarryout-n n cin a b))
    :enable (ihsext-recursive-redefs))

  (defrule plus-ucarryout-n-of-logext-n-b
    (equal (plus-ucarryout-n n cin a (logext n b))
           (plus-ucarryout-n n cin a b))
    :enable (ihsext-recursive-redefs))

  (defruled plus-carryout-n-using-preadd
    ;; This was a tricky lemma to figure out.  Of course addition modulo 32 is
    ;; perfectly associative and commutative so, when we want to compute CIN +
    ;; A + B, we can do the additions in any order.  But, when computing the
    ;; carry out we don't have this same kind of freedom.  For instance it is
    ;; not generally the case that
    ;;
    ;;   (plus-carryout-n n cin a b) == (plus-carryout-n n 0 (+ cin a) b)
    ;;
    ;; But it is *almost* true.  This lemma shows that the above is only wrong
    ;; when A is -1 and CIN is 1.  And we can easily check for these using
    ;; machine operations.
    (implies (and (posp n)
                  (bitp cin))
             (equal (plus-ucarryout-n n cin a b)
                    (if (and (equal (logext n a) -1)
                             (equal cin 1))
                        1
                      (plus-ucarryout-n n 0 (logext n (+ cin (ifix a))) b))))
    :enable (ihsext-recursive-redefs bitp b-ior b-and)
    :induct (plus-ucarryout-n n cin a b)
    :expand ((:free (cin a b) (plus-ucarryout-n n cin a b))))

  (defthm plus-ucarryout-n-of-logapp-n-left
    (equal (plus-ucarryout-n n cin (logapp n a1 a2) b)
           (plus-ucarryout-n n cin a1 b)))

  (defthm plus-ucarryout-n-of-logapp-n-right
    (equal (plus-ucarryout-n n cin a (logapp n b1 b2))
           (plus-ucarryout-n n cin a b1))))


(defsection split-plus
  :short "This is the key decomposition for big integer addition."

  (defrule split-recursive-plus
    (equal (logapp n
                   (recursive-plus cin (loghead n a) (loghead n b))
                   (recursive-plus (plus-ucarryout-n n cin a b)
                                   (logtail n a)
                                   (logtail n b)))
           (recursive-plus cin a b))
    :do-not-induct t
    :induct (plus-ucarryout-n n cin a b)
    :expand ((recursive-plus cin a b))
    :enable (ihsext-recursive-redefs
             ihsext-inductions
             recursive-plus-correct
             bitops::equal-logcons-strong)
    ;; Dumb speed hint
    :disable (equal-of-logapp-split
              zip-of-logcons
              unsigned-byte-p**
              signed-byte-p**))

  (defrule split-plus
    (implies (bitp cin)
             (equal (logapp n
                            (+ cin (loghead n a) (loghead n b))
                            (+ (plus-ucarryout-n n cin a b)
                               (logtail n a)
                               (logtail n b)))
                    (+ cin (ifix a) (ifix b))))
    :hints(("Goal"
            :use ((:instance split-recursive-plus
                   (cin (bfix cin))
                   (a   (ifix a))
                   (b   (ifix b))))
            :in-theory (e/d (recursive-plus-correct)
                            (split-recursive-plus))))))


(defsection loghead/logext-of-plus

  (local (defruled l0
           (equal (logext n (recursive-plus cin (logext n a) b))
                  (logext n (recursive-plus cin a b)))
           :enable (ihsext-recursive-redefs
                    ihsext-inductions
                    recursive-plus-base-case)))

  (defrule logext-of-plus-of-logext-left
    (implies (and (integerp a)
                  (integerp b))
             (equal (logext n (+ (logext n a) b))
                    (logext n (+ a b))))
    :use ((:instance l0 (cin 0) (a (ifix a)) (b (ifix b))))
    :enable (recursive-plus-correct))

  (local (defruled l1
           (equal (logext n (recursive-plus cin a (logext n b)))
                  (logext n (recursive-plus cin a b)))
           :enable (ihsext-recursive-redefs
                    ihsext-inductions
                    recursive-plus-base-case)))

  (defrule logext-of-plus-of-logext-right
    (implies (and (integerp a)
                  (integerp b))
             (equal (logext n (+ a (logext n b)))
                    (logext n (+ a b))))
    :use ((:instance l1 (cin 0) (a (ifix a)) (b (ifix b))))
    :enable (recursive-plus-correct))

  (local (include-book "centaur/bitops/congruences" :dir :system))
  (local (in-theory (enable* bitops-congruences)))

  (defrule loghead-of-plus-of-loghead-right
    (implies (and (integerp a)
                  (integerp b))
             (equal (loghead n (+ a (loghead n b)))
                    (loghead n (+ a b)))))

  (defrule loghead-of-plus-of-loghead-right
    (implies (and (integerp a)
                  (integerp b))
             (equal (loghead n (+ a (loghead n b)))
                    (loghead n (+ a b)))))

  (defrule |(loghead n (+ a b (loghead n c)))|
    (implies (and (integerp a)
                  (integerp b)
                  (integerp c))
             (equal (loghead n (+ a b (loghead n c)))
                    (loghead n (+ a b c))))
    :in-theory (disable loghead-of-plus-of-loghead-right)
    :use ((:instance loghead-of-plus-of-loghead-right
           (a (+ a b))
           (b c))))

  (defrule |(loghead n (+ a b (logapp n c1 c2)))|
    (implies (and (integerp a)
                  (integerp b)
                  (integerp c1))
             (equal (loghead n (+ a b (logapp n c1 c2)))
                    (loghead n (+ a b c1))))
    :use ((:instance |(loghead n (+ a b (loghead n c)))|
           (c (logapp n c1 c2))))))
