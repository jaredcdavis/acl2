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
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (std::add-default-post-define-hook :fix))

(deflist nat-list
  ;; BOZO move to fty/basetypes?
  :elt-type natp
  :pred nat-listp
  :fix nat-list-fix
  :equiv nat-list-equiv
  :no-count t
  :true-listp t)

(defsection fn
  :parents (smallexpr bigexpr)
  :short "Represents a valid function name."
  :long "<p>Syntactically, we allow most symbols to be used as function names.
         However, our expression language is fixed: only a few certain
         pre-defined @(see smallops) are actually understood.</p>"
  :autodoc nil
  (local (xdoc::set-default-parents fn))

  (define fn-p (x)
    :short "Recognizer for valid @(see fn)s."
    (and (symbolp x)
         (not (eq x 'quote))
         (not (keywordp x)))
    ///
    (defthm fn-p-compound-recognizer
      (implies (fn-p x)
               (symbolp x))
      :rule-classes :compound-recognizer))

  (define fn-fix (x)
    :short "Fixing function for @(see fn)s."
    :returns (x fn-p)
    (if (fn-p x)
        x
      'id)
    ///
    (defthm fn-fix-when-fn-p
      (implies (fn-p x)
               (equal (fn-fix x) x))))

  (defsection fn-equiv
    :short "Equivalence relation for @(see fn)s."
    (deffixtype fn
      :pred fn-p
      :fix fn-fix
      :equiv fn-equiv
      :define t
      :forward t
      :equal eq)))
