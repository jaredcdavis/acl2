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
(local (include-book "tools/do-not" :dir :system))
(local (acl2::do-not generalize fertilize))
(local (in-theory (disable signed-byte-p unsigned-byte-p)))

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


