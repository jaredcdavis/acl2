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
(include-book "smallops")
(include-book "smallexpr")
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/defval" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "std/lists/len" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defalist smallenv
  :key-type smallvar-p
  :val-type i64-p
  :true-listp t
  :parents (eval)
  :short "An alist mapping @(see smallvar)s to @(see i64)s, often used as an
          environment to @(see smalleval).")

(define smallenv-lookup ((var smallvar-p) (env smallenv-p))
  :parents (smallenv)
  :short "Look up a variable's value in an @(see smallenv). (Slow, logically nice)"
  :long "<p>This is our preferred normal form for environment lookups.  Any
            unbound variables are treated as 0.</p>"
  :returns (val i64-p)
  (mbe :logic
       (i64-fix (cdr (hons-assoc-equal (smallvar-fix var) (smallenv-fix env))))
       :exec
       (let ((look (hons-assoc-equal var env)))
         (if look
             (cdr look)
           0))))

(define smallenv-lookup-fast ((var smallvar-p) (env smallenv-p))
  :parents (smallenv)
  :short "Fast version of @(see smallenv-lookup) for environments that are @(see
          acl2::fast-alists)."
  :enabled t
  :prepwork ((local (in-theory (enable smallenv-lookup))))
  (mbe :logic (smallenv-lookup var env)
       :exec  (let ((look (hons-get var env)))
                (if look
                    (cdr look)
                  0))))


(defsection smallapply

  (defval *smalloptable*
    :short "The known @(see smallexpr) functions and their arguments."
    :long "<p>This is used to create @(see smallapply), @(see
           *smallops-to-llvm*), and so on.</p>"
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
      (i64udiv   (a b))
      (i64ite    (a b c))))

  (defun smallapply-collect-args (n max)
    (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
    (let* ((n   (nfix n))
           (max (nfix max)))
      (if (zp (- max n))
          nil
        (cons `(i64list-nth ,n args)
              (smallapply-collect-args (+ 1 n) max)))))

  (defun smallapply-cases (optable)
    (b* (((when (atom optable))
          '((otherwise
             (or (raise "Attempting to apply unknown function ~x0~%" fn)
                 0))))
         ((list fn args) (car optable))
         ;; Note: could add arity checking as in svex-apply-cases-fn
         (call `(,fn . ,(smallapply-collect-args 0 (len args)))))
      (cons `(,fn ,call)
            (smallapply-cases (cdr optable)))))

  (make-event
   `(define smallapply ((fn fn-p) (args i64list-p))
      :parents (smalleval)
      :returns (ans i64-p)
      :short "Apply an arbitrary, known function to a list of arguments."
      :long "<p>This is basically just a big case statement that lets us
             apply any ``known'' function to its arguments.</p>

             <p>Note that we extract the arguments using @(see i64list-nth),
             which effectively coerces any missing arguments to 0.</p>"
      :verbosep t
      (case (fn-fix fn) . ,(smallapply-cases *smalloptable*))
      ///
      (defrule open-smallapply-when-known
        (implies (syntaxp (quotep fn))
                 (equal (smallapply fn args)
                        (case (fn-fix fn) . ,(smallapply-cases *smalloptable*))))))))


(defines smalleval

  (define smalleval ((x smallexpr-p) (env smallenv-p))
    :parents (nativearith)
    :short "Semantics @(see smallexpr)s.  Evaluates an expression under an
            environment that gives @(see i64) values to its variables,
            producing an @(see i64)."
    :long "<p>Note that @('smalleval') is @(see memoize)d.</p>"
    :returns (val i64-p)
    :measure (smallexpr-count x)
    :verify-guards nil
    (smallexpr-case x
      :var (smallenv-lookup-fast x.var env)
      :const x.val
      :call
      (mbe :logic (smallapply x.fn (smalleval-list x.args env))
           :exec (if (eq x.fn 'i64ite)
                     ;; Short-circuit evaluation for i64ite operations.
                     ;;
                     ;; This is ugly.  It would just be:
                     ;;
                     ;;    (if (/= 0 (smalleval (first x.args) env)))
                     ;;        (smalleval (second x.args) env)
                     ;;      (smalleval (third x.args) env))
                     ;;
                     ;; But, in order to gracefully handle degenerate cases
                     ;; where we have an ITE with not enough arguments, it has
                     ;; to be uglier.
                     ;;
                     ;; In particular,
                     ;;   - smalleval-list just returns however many values it
                     ;;     is given,
                     ;;   - smallapply will turn not enough arguments into
                     ;;     zeroes.
                     ;;
                     ;; So the short story is that we have to do explicit arity
                     ;; checks to properly coerce things to zeroes.
                     (let ((a (if (consp x.args) (smalleval (first x.args) env) 0)))
                       (if (not (eql a 0))
                           (if (consp (cdr x.args)) (smalleval (second x.args) env) 0)
                         (if (consp (cddr x.args)) (smalleval (third x.args) env) 0)))
                   (smallapply x.fn (smalleval-list x.args env))))))

  (define smalleval-list ((x smallexprlist-p) (env smallenv-p))
    :returns (vals i64list-p)
    :parents (smalleval)
    :short "Evaluate a list of @(see smallexpr)s."
    :measure (smallexprlist-count x)
    (if (atom x)
        nil
      (cons (smalleval (car x) env)
            (smalleval-list (cdr x) env))))
  ///
  (deffixequiv-mutual smalleval))

(defsection smalleval-thms
  :extension (smalleval)

  (defrule smalleval-of-make-smallexpr-var
    (equal (smalleval (make-smallexpr-var :var var) env)
           (smallenv-lookup-fast var env))
    :expand ((smalleval (make-smallexpr-var :var var) env)))

  (defrule smalleval-of-make-smallexpr-const
    (equal (smalleval (make-smallexpr-const :val val) env)
           (i64-fix val))
    :expand ((smalleval (make-smallexpr-const :val val) env)))

  (defrule smalleval-of-make-smallexpr-call
    (equal (smalleval (make-smallexpr-call :fn fn :args args) env)
           (smallapply fn (smalleval-list args env)))
    :expand ((smalleval (make-smallexpr-call :fn fn :args args) env))))

(defsection smalleval-list-thms
  :extension (smalleval-list)

  (defprojection smalleval-list (x env)
    :already-definedp t
    (smalleval x env)))


;; Guards and memoization

(local (defthm i64list-nth-of-smalleval-list
         (equal (i64list-nth n (smalleval-list args env))
                (if (< (nfix n) (len args))
                    (smalleval (nth n args) env)
                  0))
         :hints(("Goal" :in-theory (enable i64list-nth)))))

(verify-guards smalleval
  :hints(("Goal" :in-theory (enable i64ite))))

(memoize 'smalleval
         :condition '(smallexpr-case x :call))
