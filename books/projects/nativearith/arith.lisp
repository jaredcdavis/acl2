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
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "centaur/fty/fixequiv" :dir :system))
(local (include-book "tools/do-not" :dir :system))
(local (acl2::do-not generalize fertilize))
(local (in-theory (disable signed-byte-p unsigned-byte-p)))
(local (std::add-default-post-define-hook :fix))

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
           ihsext-inductions))

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


(local (defthm logcar-when-not-integerp
         (implies (not (integerp a))
                  (equal (logcar a) 0))
         :hints(("Goal" :in-theory (enable logcar)))))

(local (defthm logcdr-when-not-integerp
         (implies (not (integerp a))
                  (equal (logcdr a) 0))
         :hints(("Goal" :in-theory (enable logcdr)))))


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

  (defthmd recursive-plus-base-case-correct
    (implies (and (or (zip a) (eql a -1))
                  (or (zip b) (eql b -1)))
             (equal (recursive-plus-base-case cin a b)
                    (+ (bfix cin) (ifix a) (ifix b))))
    ;; Just let things open up and prove it by cases.
    :hints(("Goal" :in-theory (enable bfix b-not b-xor b-and bitp zip logcar))))

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
  (local (defthmd inductive-step
           (let* ((a0   (logcar a))
                  (b0   (logcar b))
                  (sum  (b-xor cin (b-xor a0 b0)))
                  (cout (b-ior (b-and a0 b0)
                               (b-and cin (b-ior a0 b0))))
                  (rest (+ cout (logcdr a) (logcdr b))))
             (equal (logcons sum rest)
                    (+ (bfix cin) (ifix a) (ifix b))))
           :hints(("Goal"
                   :in-theory (e/d (b-ior b-and b-xor b-not)
                                   (bitops::+-of-logcons-with-cin))
                   :use ((:instance bitops::+-of-logcons-with-cin
                          (cin (bfix cin))
                          (b1 (logcar a))
                          (r1 (logcdr a))
                          (b2 (logcar b))
                          (r2 (logcdr b))))))))

  (defruled recursive-plus-correct
    (equal (recursive-plus cin a b)
           (+ (bfix cin) (ifix a) (ifix b)))
    :hints(("Goal"
            :induct (recursive-plus cin a b)
            :in-theory (enable recursive-plus-base-case-correct))
           ("Subgoal *1/2" ;; Baaaah, can't get rid of it!
            :use ((:instance inductive-step)))))

  (verify-guards recursive-plus$inline
    :hints(("Goal" :use ((:instance recursive-plus-correct))))))


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
  (defthm plus-ucarryout-n-of-loghead-n-a
    (equal (plus-ucarryout-n n cin (loghead n a) b)
           (plus-ucarryout-n n cin a b))
    :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs))))

  (defthm plus-ucarryout-n-of-loghead-n-b
    (equal (plus-ucarryout-n n cin a (loghead n b))
           (plus-ucarryout-n n cin a b))
    :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs))))

  (defthmd plus-ucarryout-n-as-unsigned-byte-p
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
                                b-not)))))

(defsection split-unsigned-plus

  (local (acl2::do-not generalize fertilize eliminate-destructors))

  (defthm split-unsigned-recursive-plus
    (implies (and (natp a)
                  (natp b)
                  (natp n))
             (equal (logapp n
                            (recursive-plus cin (loghead n a) (loghead n b))
                            (recursive-plus (plus-ucarryout-n n cin (loghead n a) (loghead n b))
                                            (logtail n a)
                                            (logtail n b)))
                    (recursive-plus cin a b)))
    :hints(("Goal"
            :do-not-induct t
            :induct (plus-ucarryout-n n cin a b)
            :expand ((recursive-plus cin a b)
                     (recursive-plus cin (loghead n a) (loghead n b))
                     (plus-ucarryout-n n cin (loghead n a) (loghead n b)))
            :in-theory (enable* ihsext-recursive-redefs
                                recursive-plus
                                plus-ucarryout-n
                                recursive-plus-base-case))))

  (defthm split-unsigned-plus
    (implies (and (natp a)
                  (natp b)
                  (natp n)
                  (bitp cin))
             (equal (logapp n
                            (+ cin (loghead n a) (loghead n b))
                            (+ (plus-ucarryout-n n cin a b)
                               (logtail n a)
                               (logtail n b)))
                    (+ cin a b)))
    :hints(("Goal"
            :in-theory (e/d (recursive-plus-correct)
                            (split-unsigned-recursive-plus))
            :use ((:instance split-unsigned-recursive-plus))))))



zz i-am-here


(local (acl2::do-not generalize fertilize eliminate-destructors))



(let* ((a -1)
       (b -7)
       (cin 0)
       (n 4)
       (spec (recursive-plus cin a b))
       (head (recursive-plus cin (loghead n a) (loghead n b)))
       (cout (plus-ucarryout-n n cin (loghead n a) (loghead n b)))
       (tail (recursive-plus cout (logtail n a) (logtail n b)))
       (impl (logapp n head tail)))
  (list :spec spec
        :head head
        :cout cout
        :tail tail
        :impl impl))

  (list (recursive-plus 0 -1 -1)
        (logapp n
                (recursive-plus cin (loghead n a) (loghead n b))
                (recursive-plus (plus-ucarryout-n n cin (loghead n a) (loghead n b))
                                (logtail n a)
                                (logtail n b)))



(include-book "acl2s/cgen/top" :dir :system)

(defthm minus-of-minus
  (equal (- (- n))
         (fix n)))



(defthm zip-of-logcons
  (equal (zip (logcons a x))
         (and (not (eql a 1))
              (zip x))))


(defthm xx
  (implies (and (integerp x)
                (integerp y))
           (equal (equal (logcons a x) y)
                  (and (equal (logcar y) (bfix a))
                       (equal (logcdr y) (ifix x))))))

(defthm equal-logcons-and-loghead
  (implies (posp n)
           (equal (equal (logcons a x)
                         (loghead n y))
                  (and (equal (bfix a) (logcar y))
                       (equal (ifix x) (loghead (- n 1) (logcdr y))))))
  :hints(("Goal"
          :in-theory (enable* ihsext-recursive-redefs))))

(defun my-induct (n a b)
  (if (zp n)
      (list n a b)
    (my-induct (- n 1) (logcdr a) (logcdr b))))

(defthm l0
  (equal (loghead n (recursive-plus cin (loghead n a) b))
         (loghead n (recursive-plus cin a b)))
  :hints(("Goal" :induct (my-induct n a b)
          :in-theory (enable* recursive-plus
                              ihsext-recursive-redefs))))
                              bitops-congruences))))
                                    

(defthm split-signed-recursive-plus
    (implies (and (integerp a)
                  (integerp b)
                  (natp n))
             (equal (logapp n
                            (recursive-plus cin (loghead n a) (loghead n b))
                            (recursive-plus (plus-ucarryout-n n cin (loghead n a) (loghead n b))
                                            (logtail n a)
                                            (logtail n b)))
                    (recursive-plus cin a b)))
    :hints(("Goal"
            :do-not-induct t
            :induct (plus-ucarryout-n n cin a b)
            :expand ((recursive-plus cin a b)
                     (recursive-plus cin (loghead n a) (loghead n b))
                     (plus-ucarryout-n n cin (loghead n a) (loghead n b)))
            :in-theory (e/d* (ihsext-recursive-redefs
                              recursive-plus
                              plus-ucarryout-n
                              recursive-plus-base-case)
                             (acl2::zip-open)
                             ))))

