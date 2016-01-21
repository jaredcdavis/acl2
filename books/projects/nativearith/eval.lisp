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
(include-book "ops")
(include-book "expr")
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defalist env
  :key-type var-p
  :val-type i64-p
  :true-listp t
  :parents (eval)
  :short "An alist mapping @(see var)s to @(see i64)s, often used as an
          environment to @(see eval).")

(define env-lookup ((var var-p) (env env-p))
  :parents (env)
  :short "Look up a variable's value in an @(see env). (Slow, logically nice)"
  :long "<p>This is our preferred normal form for environment lookups.  Any
            unbound variables are treated as 0.</p>"
  :returns (val i64-p)
  (mbe :logic
       (i64-fix (cdr (hons-assoc-equal (var-fix var) (env-fix env))))
       :exec
       (let ((look (hons-assoc-equal var env)))
         (if look
             (cdr look)
           0))))

(define env-lookup-fast ((var var-p) (env env-p))
  :parents (env)
  :short "Fast version of @(see env-lookup) for environments that are @(see
          acl2::fast-alists)."
  :enabled t
  :prepwork ((local (in-theory (enable env-lookup))))
  (mbe :logic (env-lookup var env)
       :exec  (let ((look (hons-get var env)))
                (if look
                    (cdr look)
                  0))))


(defsection apply

  (defconst *optable*
    '((i64bitnot (a))
      (i64sminus (a))
      (i64eql    (a b))
      (i64neq    (a b))
      (i64slt    (a b))
      (i64sle    (a b))
      (i64sgt    (a b))
      (i64sge    (a b))
      (i64ult    (a b))
      (i64ule    (a b))
      (i64ugt    (a b))
      (i64uge    (a b))
      (i64bitand (a b))
      (i64bitor  (a b))
      (i64plus   (a b))
      (i64minus  (a b))
      (i64times  (a b))
      (i64sdiv   (a b))
      (i64udiv   (a b))))

  (defun apply-collect-args (n max)
    (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
    (let* ((n   (nfix n))
           (max (nfix max)))
      (if (zp (- max n))
          nil
        (cons `(i64list-nth ,n args)
              (apply-collect-args (+ 1 n) max)))))

  (defun apply-cases (optable)
    (b* (((when (atom optable))
          '((otherwise
             (or (raise "Attempting to apply unknown function ~x0~%" fn)
                 0))))
         ((list fn args) (car optable))
         ;; Note: could add arity checking as in svex-apply-cases-fn
         (call `(,fn . ,(apply-collect-args 0 (len args)))))
      (cons `(,fn ,call)
            (apply-cases (cdr optable)))))

  (make-event
   `(define apply ((fn fn-p) (args i64list-p))
      :parents (eval)
      :returns (ans i64-p)
      :short "Apply an arbitrary, known function to a list of arguments."
      :long "<p>This is basically just a big case statement that lets us
             apply any ``known'' function to its arguments.</p>

             <p>Note that we extract the arguments using @(see i64list-nth),
             which effectively coerces any missing arguments to 0.</p>"
      :verbosep t
      (case (fn-fix fn) . ,(apply-cases *optable*))
      ///
      (defthm open-apply-when-known
        (implies (syntaxp (quotep fn))
                 (equal (apply fn args)
                        (case (fn-fix fn) . ,(apply-cases *optable*))))))))


(defines eval

  (define eval ((x expr-p) (env env-p))
    :parents (nativearith)
    :short "Semantics of expressions."
    :returns (val i64-p)
    :measure (expr-count x)
    :verify-guards nil
    ;; This is really nice, but eventually we will probably want to complicate
    ;; it so that we can have short-circuit evaluation of IF, etc.
    (expr-case x
      :var (env-lookup-fast x.name env)
      :const x.val
      :call (apply x.fn (eval-list x.args env))))

  (define eval-list ((x exprlist-p) (env env-p))
    :returns (vals i64list-p)
    :measure (exprlist-count x)
    (if (atom x)
        nil
      (cons (eval (car x) env)
            (eval-list (cdr x) env))))
  ///
  (verify-guards eval)
  (deffixequiv-mutual eval)

  (defthm eval-of-make-expr-var
    (equal (eval (make-expr-var :name name) env)
           (env-lookup-fast name env))
    :hints(("Goal" :expand ((eval (make-expr-var :name name) env)))))

  (defthm eval-of-make-expr-const
    (equal (eval (make-expr-const :val val) env)
           (i64-fix val))
    :hints(("Goal" :expand ((eval (make-expr-const :val val) env)))))

  (defthm eval-of-make-expr-call
    (equal (eval (make-expr-call :fn fn :args args) env)
           (apply fn (eval-list args env)))
    :hints(("Goal" :expand ((eval (make-expr-call :fn fn :args args) env)))))

  (defthm eval-list-when-atom
    (implies (atom x)
             (equal (eval-list x env)
                    nil))
    :hints(("Goal" :expand ((eval-list x env)))))

  (defthm eval-list-of-cons
    (equal (eval-list (cons a x) env)
           (cons (eval a env)
                 (eval-list x env)))
    :hints(("Goal" :expand ((eval-list (cons a x) env))))))








