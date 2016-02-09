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
(include-book "std/basic/defs" :dir :system)
(include-book "centaur/fty/fixtype" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
;; BOZO consider integrating this all into centaur/fty/basetypes

(defthm maybe-integerp-when-integerp
  ;; BOZO non-local, move to std/defs instead?
  (implies (integerp x)
           (maybe-integerp x)))

(defthmd integerp-when-maybe-integerp
  ;; BOZO non-local, move to std/defs instead?
  (implies (and (maybe-integerp x)
                (double-rewrite x))
           (integerp x)))

(defsection maybe-integerp-fix
  :parents (maybe-integerp)
  :short "@(call maybe-integerp-fix) is the identity for @(see
  maybe-integerp)s, or coerces any invalid object to @('nil')."
  :long "<p>Performance note.  In the execution this is just an inlined
  identity function, i.e., it should have zero runtime cost.</p>"

  (defund-inline maybe-integerp-fix (x)
    (declare (xargs :guard (maybe-integerp x)))
    (mbe :logic (if x (ifix x) nil)
         :exec x))

  (local (in-theory (enable maybe-integerp-fix)))

  (defthm maybe-integerp-of-maybe-integerp-fix
    (maybe-integerp (maybe-integerp-fix x))
    :rule-classes (:rewrite :type-prescription))

  (defthm maybe-integerp-fix-when-maybe-integerp
    (implies (maybe-integerp x)
             (equal (maybe-integerp-fix x) x)))

  (defthm maybe-integerp-fix-under-iff
    (iff (maybe-integerp-fix x) x))

  (defthm maybe-integerp-fix-under-int-equiv
    (int-equiv (maybe-integerp-fix x) x)
    :hints(("Goal" :in-theory (enable maybe-integerp-fix)))))


(defsection maybe-int-equiv
  :parents (maybe-integerp)
  :short "@('(maybe-integerp-equiv x y)') is an equivalence relation for @(see
  maybe-integerp)s, i.e., equality up to @(see maybe-integerp-fix)."
  :long "<p>Performance note.  In the execution, this is just an inlined call
  of @(see eql).</p>"

  (deffixtype maybe-nat
    :pred maybe-integerp
    :fix maybe-integerp-fix
    :equiv maybe-int-equiv
    :define t
    :inline t
    :equal eql
    :topic maybe-integerp))
