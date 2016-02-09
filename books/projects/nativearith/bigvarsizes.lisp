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
(include-book "bigeval")
(local (include-book "std/alists/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable signed-byte-p)))

(defalist bigvarsizes
  :key-type bigvar-p
  :val-type posp
  :short "Size bounds for the variables in a @(see bigexpr)."

  :long "<p>To statically compile @(see bigexpr)s into @(see smallexpr)s we
need to be able to bound the size of all subexpressions.  To evaluate
operations like @($a = b$) or @($a < b$), we need to have bounds for the
variables.</p>

<p>A @('bigvarsizes') is a mapping from variables to size bounds.  We require
that each size bound be at least 1, since variable of size 0 don't especially
make sense and also since @(see logext) does not behave very sensibly when its
size argument is 0 and @(see signed-byte-p) does not tolerate 0 sizes.</p>")

(local (xdoc::set-default-parents bigvarsizes))


(define bigvarsize-lookup ((var      bigvar-p)
                           (varsizes bigvarsizes-p))
  :short "Look up the size bound for a variable."
  :long "<p>Any unbound variables are given size 1.</p>"
  :returns (size posp :rule-classes :type-prescription)
  (mbe :logic
       (b* ((var      (bigvar-fix var))
            (varsizes (bigvarsizes-fix varsizes)))
         (pos-fix (cdr (hons-assoc-equal var varsizes))))
       :exec
       (let ((look (hons-get var varsizes)))
         (if look
             (cdr look)
           1))))

(define bigenv-var-sizeok-p ((var bigvar-p)
                             (env bigenv-p)
                             (varsizes bigvarsizes-p))
  :parents (bigenv-sizeok-p)
  :short "Single variable version of: is @('env[var]') in bounds?"
  :returns (okp booleanp :rule-classes :type-prescription)
  (b* ((env[var]   (bigenv-lookup-fast var env))
       (sizes[var] (bigvarsize-lookup var varsizes)))
    (signed-byte-p sizes[var] (bigint->val env[var])))
  ///
  (defrule bigenv-var-sizeok-p-when-zero
    (implies (equal (bigenv-lookup var env) (bigint-0))
             (bigenv-var-sizeok-p var env varsizes))))


(define bigenv-varlist-sizeok-p ((vars     bigvarlist-p)
                                 (env      bigenv-p)
                                 (varsizes bigvarsizes-p))
  :parents (bigenv-sizeok-p)
  :short "Variable list version of: is @('env[var]') in bounds?"
  :returns (okp booleanp :rule-classes :type-prescription)
  (or (atom vars)
      (and (bigenv-var-sizeok-p (car vars) env varsizes)
           (bigenv-varlist-sizeok-p (cdr vars) env varsizes)))
  ///
  (defrule bigenv-varlist-sizeok-p-when-atom
    (implies (atom vars)
             (bigenv-varlist-sizeok-p vars env varsizes)))
  (defrule bigenv-varlist-sizeok-p-of-cons
    (equal (bigenv-varlist-sizeok-p (cons var vars) env varsizes)
           (and (bigenv-var-sizeok-p var env varsizes)
                (bigenv-varlist-sizeok-p vars env varsizes))))
  (defrule bigenv-var-sizeok-p-when-member-and-bigenv-varlist-sizeok-p
    (implies (and (bigenv-varlist-sizeok-p vars env varsizes)
                  (member var vars))
             (bigenv-var-sizeok-p var env varsizes))))


(define bigenv-sizeok-p ((env      bigenv-p)
                         (varsizes bigvarsizes-p))
  :short "Is @('env[var]') in bounds for all @('var')?"
  :returns (okp booleanp :rule-classes :type-prescription)
  (b* ((env (bigenv-fix env)))
    (bigenv-varlist-sizeok-p (alist-keys env) env varsizes))
  ///
  (local (in-theory (e/d (acl2::hons-assoc-equal-iff-member-alist-keys)
                         (acl2::alist-keys-member-hons-assoc-equal))))

  (local (defrule l1
           (implies (not (member (bigvar-fix var) (alist-keys (bigenv-fix env))))
                    (equal (bigenv-lookup var env)
                           (bigint-0)))
           :enable bigenv-lookup))

  "<p>Main theorem: If the whole environment satisfies these bounds,
   then every variable satisfies the bounds (whether it's bound or not).</p>"

  (defrule bigenv-var-sizeok-p-when-bigenv-sizeok-p
    (implies (bigenv-sizeok-p env varsizes)
             (bigenv-var-sizeok-p var env varsizes))
    :enable (bigenv-var-sizeok-p)
    :cases ((member (bigvar-fix var) (alist-keys (bigenv-fix env))))
    :disable (bigenv-var-sizeok-p-when-member-and-bigenv-varlist-sizeok-p)
    :use ((:instance bigenv-var-sizeok-p-when-member-and-bigenv-varlist-sizeok-p
           (var (bigvar-fix var))
           (vars (alist-keys (bigenv-fix env))))))

  "<p>Easy corollary, which lets us use @(see bigenv-sizeok-p) to deduce @(see
   signed-byte-p) directly for any variable lookup.</p>"

  (defrule signed-byte-p-of-bigvarsize-lookup-in-bigenv-lookup
    (implies (bigenv-sizeok-p env varsizes)
             (signed-byte-p (bigvarsize-lookup var varsizes)
                            (bigint->val (bigenv-lookup var env))))
    :disable (bigenv-var-sizeok-p-when-bigenv-sizeok-p)
    :use ((:instance bigenv-var-sizeok-p-when-bigenv-sizeok-p))
    :enable bigenv-var-sizeok-p))
