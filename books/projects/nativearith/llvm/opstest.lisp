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
(include-book "ops")
(include-book "system/random" :dir :system)
(include-book "std/typed-lists/signed-byte-listp" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

(defconst *interesting-numbers*
  (list 0 1 2 3 4 5
        -5 -4 -3 -2 -1

        28 29 30 31 32 33 34
        61 62 63 64 65 66 67

        (- (expt 2 16))
        (+ 1 (- (expt 2 16)))
        (+ 2 (- (expt 2 16)))
        (+ 3 (- (expt 2 16)))
        (+ 4 (- (expt 2 16)))
        (+ -1 (expt 2 16))
        (+ -2 (expt 2 16))
        (+ -3 (expt 2 16))
        (+ -4 (expt 2 16))
        (+ -5 (expt 2 16))

        (- (expt 2 15))
        (+ 1 (- (expt 2 15)))
        (+ 2 (- (expt 2 15)))
        (+ 3 (- (expt 2 15)))
        (+ 4 (- (expt 2 15)))
        (+ -1 (expt 2 15))
        (+ -2 (expt 2 15))
        (+ -3 (expt 2 15))
        (+ -4 (expt 2 15))
        (+ -5 (expt 2 15))

        (- (expt 2 32))
        (+ 1 (- (expt 2 32)))
        (+ 2 (- (expt 2 32)))
        (+ 3 (- (expt 2 32)))
        (+ 4 (- (expt 2 32)))
        (+ -1 (expt 2 32))
        (+ -2 (expt 2 32))
        (+ -3 (expt 2 32))
        (+ -4 (expt 2 32))
        (+ -5 (expt 2 32))

        (- (expt 2 31))
        (+ 1 (- (expt 2 31)))
        (+ 2 (- (expt 2 31)))
        (+ 3 (- (expt 2 31)))
        (+ 4 (- (expt 2 31)))
        (+ -1 (expt 2 31))
        (+ -2 (expt 2 31))
        (+ -3 (expt 2 31))
        (+ -4 (expt 2 31))
        (+ -5 (expt 2 31))

        (- (expt 2 63))
        (+ 1 (- (expt 2 63)))
        (+ 2 (- (expt 2 63)))
        (+ 3 (- (expt 2 63)))
        (+ 4 (- (expt 2 63)))
        (+ -1 (expt 2 63))
        (+ -2 (expt 2 63))
        (+ -3 (expt 2 63))
        (+ -4 (expt 2 63))
        (+ -5 (expt 2 63))
        ))

(defmacro test-unaryop (op)
  (let ((narith-op (intern$ (cat "NARITH-" (symbol-name op)) "NATIVEARITH"))
        (test-op (intern$ (cat "TEST-" (symbol-name op)) "NATIVEARITH"))
        (test-op-crafted (intern$ (cat "TEST-" (symbol-name op) "-CRAFTED") "NATIVEARITH"))
        (test-op-random (intern$ (cat "TEST-" (symbol-name op) "-RANDOM") "NATIVEARITH")))
    `(with-output
       :off :all
       :gag-mode t
       :on (error)
       (progn
         (local (xdoc::set-default-parents ,narith-op))
         (local (in-theory (enable i64-p)))
         (define ,test-op ((a i64-p :type (signed-byte 64)))
           :split-types t
           (b* ((spec (,op a))
                (impl (,narith-op a)))
             (or (equal spec impl)
                 (raise "Mismatch for (~s0 ~x1): spec is ~x2 but impl got ~x3."
                        ',op a spec impl))))

         (define ,test-op-crafted ((as i64list-p))
           (or (atom as)
               (and (,test-op (car as))
                    (,test-op-crafted (cdr as)))))

         (define ,test-op-random ((n natp) state)
           (b* (((when (zp n))
                 (mv t state))
                ((mv rnd state) (random$ (expt 2 64) state))
                ((unless (,test-op (fast-logext 64 rnd)))
                 (mv nil state)))
             (,test-op-random (- n 1) state)))

         (make-event
          (b* ((okp (time$ (,test-op-crafted *interesting-numbers*)
                           :msg "Crafted tests of ~s0: ~st sec, ~sa bytes~%"
                           :args (list ',op)))
               ((unless okp)
                (er soft 'test-unaryop "Test failed"))
               ((mv okp state) (time$ (,test-op-random 100000 state)
                                      :msg "Random tests of ~s0: ~st sec, ~sa bytes~%"
                                      :args (list ',op)))
               ((unless okp)
                (er soft 'test-unaryop "Test failed")))
            (value '(value-triple :success))))))))

(test-unaryop i64bitnot)
(test-unaryop i64sminus)


(defmacro test-binop (op)
  (let ((narith-op (intern$ (cat "NARITH-" (symbol-name op)) "NATIVEARITH"))
        (test-op (intern$ (cat "TEST-" (symbol-name op)) "NATIVEARITH"))
        (test-op-crafted1 (intern$ (cat "TEST-" (symbol-name op) "-CRAFTED1") "NATIVEARITH"))
        (test-op-crafted2 (intern$ (cat "TEST-" (symbol-name op) "-CRAFTED2") "NATIVEARITH"))
        (test-op-crafted (intern$ (cat "TEST-" (symbol-name op) "-CRAFTED") "NATIVEARITH"))
        (test-op-random (intern$ (cat "TEST-" (symbol-name op) "-RANDOM") "NATIVEARITH"))
        )

    `(with-output
       :off :all
       :gag-mode t
       :on (error)
       (progn
         (local (xdoc::set-default-parents ,narith-op))
         (local (in-theory (enable i64-p)))

         (define ,test-op ((a i64-p :type (signed-byte 64))
                           (b i64-p :type (signed-byte 64)))
           :split-types t
           (b* ((spec (,op a b))
                (impl (,narith-op a b)))
             (or (equal spec impl)
                 (raise "Mismatch for (~s0 ~x1 ~x2): spec is ~x3 but impl got ~x4."
                        ',op a b spec impl))))

         (define ,test-op-crafted1 ((a i64-p)
                                    (bs i64list-p))
           (or (atom bs)
               (and (,test-op a (car bs))
                    (,test-op-crafted1 a (cdr bs)))))

         (define ,test-op-crafted2 ((as i64list-p)
                                    (bs i64list-p))
           (or (atom as)
               (and (,test-op-crafted1 (car as) bs)
                    (,test-op-crafted2 (cdr as) bs))))

         (define ,test-op-crafted ((x i64list-p))
           (,test-op-crafted2 x x))

         (define ,test-op-random ((n natp) state)
           (b* (((when (zp n))
                 (mv t state))
                ((mv rnd1 state) (random$ (expt 2 64) state))
                ((mv rnd2 state) (random$ (expt 2 64) state))
                ((unless (,test-op (fast-logext 64 rnd1) (fast-logext 64 rnd2)))
                 (mv nil state)))
             (,test-op-random (- n 1) state)))

         (make-event
          (b* ((okp (time$ (,test-op-crafted *interesting-numbers*)
                           :msg "Crafted tests of ~s0: ~st sec, ~sa bytes~%"
                           :args (list ',op)))
               ((unless okp)
                (er soft 'test-binop "Test failed"))
               ((mv okp state) (time$ (,test-op-random 100000 state)
                                      :msg "Random tests of ~s0: ~st sec, ~sa bytes~%"
                                      :args (list ',op)))
               ((unless okp)
                (er soft 'test-binop "Test failed")))
            (value '(value-triple :success))))))))

(test-binop i64eql)
(test-binop i64neq)

(test-binop i64sle)
(test-binop i64slt)
(test-binop i64sge)
(test-binop i64sgt)

(test-binop i64ule)
(test-binop i64ult)
(test-binop i64uge)
(test-binop i64ugt)

(test-binop i64bitand)
(test-binop i64bitor)
(test-binop i64bitxor)
(test-binop i64plus)
(test-binop i64minus)
(test-binop i64times)

(test-binop i64sdiv)
(test-binop i64udiv)

