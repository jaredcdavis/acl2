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
(include-book "bigops")
(include-book "bigexpr")
(local (std::add-default-post-define-hook :fix))

(defalist bigenv
  :key-type var-p
  :val-type bigint-p
  :true-listp t
  :parents (bigeval)
  :short "An alist mapping @(see var)s to @(see bigint)s, often used as an
          environment to @(see bigeval).")

(define bigenv-lookup ((var var-p) (env bigenv-p))
  :parents (bigenv)
  :short "Look up a variable's value in an @(see bigenv). (Slow, logically nice)"
  :long "<p>This is our preferred normal form for environment lookups.  Any
            unbound variables are treated as 0.</p>"
  :returns (val bigint-p)
  (mbe :logic
       (bigint-fix (cdr (hons-assoc-equal (var-fix var) (bigenv-fix env))))
       :exec
       (let ((look (hons-assoc-equal var env)))
         (if look
             (cdr look)
           (bigint-0)))))

(define bigenv-lookup-fast ((var var-p) (env bigenv-p))
  :parents (bigenv)
  :short "Fast version of @(see bigenv-lookup) for environments that are @(see
          acl2::fast-alists)."
  :enabled t
  :prepwork ((local (in-theory (enable bigenv-lookup))))
  (mbe :logic (bigenv-lookup var env)
       :exec  (let ((look (hons-get var env)))
                (if look
                    (cdr look)
                  (bigint-0)))))

(defsection bigapply

  (defconst *bigoptable*
    '((bigint-lognot (a))
      (bigint-logior (a b))
      (bigint-logand (a b))
      (bigint-logxor (a b))
      (bigint-equal (a b))
      (bigint-not-equal (a b))
      (bigint-slt (a b))
      (bigint-sle (a b))
      (bigint-sgt (a b))
      (bigint-sge (a b))))

  (defun bigapply-collect-args (n max)
    (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
    (let* ((n   (nfix n))
           (max (nfix max)))
      (if (zp (- max n))
          nil
        (cons `(bigintlist-nth ,n args)
              (bigapply-collect-args (+ 1 n) max)))))

  (defun bigapply-cases (optable)
    (b* (((when (atom optable))
          '((otherwise
             (or (raise "Attempting to apply unknown function ~x0~%" fn)
                 (bigint-0)))))
         ((list fn args) (car optable))
         ;; Note: could add arity checking as in svex-bigapply-cases-fn
         (call `(,fn . ,(bigapply-collect-args 0 (len args)))))
      (cons `(,fn ,call)
            (bigapply-cases (cdr optable)))))

  (make-event
   `(define bigapply ((fn fn-p) (args bigintlist-p))
      :parents (bigeval)
      :returns (ans bigint-p)
      :short "Apply an arbitrary, known @(see bigops) function to a list of
              arguments."
      :long "<p>This is basically just a big case statement that lets us apply
             any ``known'' function to its arguments.  For the list of known
             functions, see @(see bigops).</p>

             <p>Note that we extract the arguments using @(see bigintlist-nth),
             which effectively coerces any missing arguments to @(see
             bigint-0).</p>"
      :verbosep t
      (case (fn-fix fn) . ,(bigapply-cases *bigoptable*))
      ///
      (defthm open-bigapply-when-known
        (implies (syntaxp (quotep fn))
                 (equal (bigapply fn args)
                        (case (fn-fix fn) . ,(bigapply-cases *bigoptable*))))))))

(defines bigeval

  (define bigeval ((x bigexpr-p) (env bigenv-p))
    :parents (nativearith)
    :short "Semantics of @(see bigexpr)s.  Evaluates an expression under an
            environment that gives @(see bigint) values to its variables,
            producing a bigint."
    :returns (val bigint-p)
    :measure (bigexpr-count x)
    :verify-guards nil
    ;; This is really nice, but eventually we will probably want to complicate
    ;; it so that we can have short-circuit evaluation of IF, etc.
    (bigexpr-case x
      :var (bigenv-lookup-fast x.name env)
      :const x.val
      :call (bigapply x.fn (bigeval-list x.args env))))

  (define bigeval-list ((x bigexprlist-p) (env bigenv-p))
    :returns (vals bigintlist-p)
    :measure (bigexprlist-count x)
    (if (atom x)
        nil
      (cons (bigeval (car x) env)
            (bigeval-list (cdr x) env))))
  ///
  (verify-guards bigeval)
  (deffixequiv-mutual bigeval)

  (defthm bigeval-of-make-bigexpr-var
    (equal (bigeval (make-bigexpr-var :name name) env)
           (bigenv-lookup-fast name env))
    :hints(("Goal" :expand ((bigeval (make-bigexpr-var :name name) env)))))

  (defthm bigeval-of-make-bigexpr-const
    (equal (bigeval (make-bigexpr-const :val val) env)
           (bigint-fix val))
    :hints(("Goal" :expand ((bigeval (make-bigexpr-const :val val) env)))))

  (defthm bigeval-of-make-bigexpr-call
    (equal (bigeval (make-bigexpr-call :fn fn :args args) env)
           (bigapply fn (bigeval-list args env)))
    :hints(("Goal" :expand ((bigeval (make-bigexpr-call :fn fn :args args) env)))))

  (defthm bigeval-list-when-atom
    (implies (atom x)
             (equal (bigeval-list x env)
                    nil))
    :hints(("Goal" :expand ((bigeval-list x env)))))

  (defthm bigeval-list-of-cons
    (equal (bigeval-list (cons a x) env)
           (cons (bigeval a env)
                 (bigeval-list x env)))
    :hints(("Goal" :expand ((bigeval-list (cons a x) env))))))








