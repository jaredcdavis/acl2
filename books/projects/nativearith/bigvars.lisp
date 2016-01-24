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
(include-book "bigexpr")
(local (std::add-default-post-define-hook :fix))

(deflist bigvarlist
  :elt-type bigvar
  :true-listp t
  :elementp-of-nil nil)

(defines bigexpr-vars
  :parents (bigexpr)
  :short "Logically nice (but inefficient) way to collect variables from @(see
          bigexpr)s."

  (define bigexpr-vars ((x bigexpr-p))
    :returns (vars bigvarlist-p)
    :measure (bigexpr-count x)
    ;; We don't expect to ever run this.  But just in case, we put timing
    ;; messages in here so that if we ever run this by accident, we're likely
    ;; to notice it.
    (time$ (bigexpr-case x
             :const nil
             :var (list x.name)
             :call (bigexprlist-vars x.args))
           :mintime 1
           :msg "bigexpr-vars: ~st sec, ~sa bytes.~%"))

  (define bigexprlist-vars ((x bigexprlist-p))
    :parents (bigexpr-vars)
    :returns (vars bigvarlist-p)
    :measure (bigexprlist-count x)
    (if (atom x)
        nil
      (append (bigexpr-vars (car x))
              (bigexprlist-vars (cdr x)))))
  ///
  (deffixequiv-mutual bigexpr-vars))


(defines bigexpr-vars-memofal
  :parents (fast-bigexpr-vars)
  :short "Efficient algorithm for collecting elements from nodes."

  (define bigexpr-vars-memofal ((x bigexpr-p) seenfal ans)
    :returns (mv new-seenfal
                 (new-ans bigvarlist-p :hyp (bigvarlist-p ans)))
    :measure (bigexpr-count x)
    (b* ((kind (bigexpr-kind x))
         ((when (eq kind :const))
          ;; Too trivial, don't even want to mark it as seen.
          (mv seenfal ans))
         ((when (hons-get x seenfal))
          (mv seenfal ans))
         (seenfal (hons-acons x t seenfal))
         ((when (eq kind :var))
          (mv seenfal (cons (bigexpr-var->name x) ans))))
      (bigexprlist-vars-memofal (bigexpr-call->args x) seenfal ans)))

  (define bigexprlist-vars-memofal ((x bigexprlist-p) seenfal ans)
    :measure (bigexprlist-count x)
    :returns (mv new-seenfal
                 (new-ans bigvarlist-p :hyp (bigvarlist-p ans)))
    (b* (((when (atom x))
          (mv seenfal ans))
         ((mv seenfal ans) (bigexpr-vars-memofal (car x) seenfal ans)))
      (bigexprlist-vars-memofal (cdr x) seenfal ans)))

  ///
  ;; Proof of correctness using the generic node-collect-triv proof.
  ;; Almost plug-and-play, but we need a slightly modified count.

  (local (include-book "node-collect-triv"))
  (local (defines my-count
           :verify-guards nil
           (define my-count (x)
             :measure (bigexpr-count x)
             (bigexpr-case x
               :const 1
               :var 1
               :call (+ 1 (my-count-list x.args))))
           (define my-count-list (x)
             :measure (bigexprlist-count x)
             (if (atom x)
                 0
               (+ 1 (my-count (car x))
                  (my-count-list (cdr x)))))))

  (local (defthm l1
           (implies (and (not (equal (bigexpr-kind node) :const))
                         (not (equal (bigexpr-kind node) :var)))
                    (< (my-count-list (bigexpr-call->args node))
                       (my-count node)))
           :hints(("Goal" :expand ((my-count node))))))

  (local (in-theory (enable bigexpr-vars-memofal
                            bigexprlist-vars-memofal
                            bigexpr-vars
                            bigexprlist-vars
                            my-count-list)))

  (make-event
   (let ((fi-pairs
          '((nct-node-trivial             (lambda (x) (bigexpr-case x :const)))
            (nct-node-children            (lambda (x) (bigexpr-case x
                                                        :const nil
                                                        :var nil
                                                        :call x.args)))
            (nct-node-elems               (lambda (x) (bigexpr-case x
                                                        :const nil
                                                        :var (list x.name)
                                                        :call nil)))
            (nct-node-count               (lambda (x) (my-count x)))
            (nct-nodelist-count           (lambda (x) (my-count-list x)))
            (nct-node-collect             (lambda (x) (bigexpr-vars x)))
            (nct-nodelist-collect         (lambda (x) (bigexprlist-vars x)))
            (nct-node-collect-memofal     (lambda (x seen ans) (bigexpr-vars-memofal x seen ans)))
            (nct-nodelist-collect-memofal (lambda (x seen ans) (bigexprlist-vars-memofal x seen ans))))))
     `(progn
        (defthm bigexpr-vars-memofal-correct
          (b* (((mv ?new-seenlst new-ans) (bigexpr-vars-memofal x nil ans)))
            (set-equiv new-ans (append ans (bigexpr-vars x))))
          :hints(("Goal"
                  :use ((:functional-instance nct-node-collect-memofal-correct
                         . ,fi-pairs)))))

        (defthm bigexprlist-vars-memofal-correct
          (b* (((mv ?new-seenlst new-ans) (bigexprlist-vars-memofal x nil ans)))
            (set-equiv new-ans (append ans (bigexprlist-vars x))))
          :hints(("Goal"
                  :use ((:functional-instance nct-nodelist-collect-memofal-correct
                         . ,fi-pairs)))))))))

(define fast-bigexpr-vars ((x bigexpr-p))
  :returns (vars bigvarlist-p)
  (b* (((mv seenlst ans)
        (bigexpr-vars-memofal (bigexpr-fix x) nil nil)))
    (fast-alist-free seenlst)
    ans)
  ///
  (defthm fast-bigexpr-vars-elim
    (set-equiv (fast-bigexpr-vars x)
               (bigexpr-vars x))))

(define fast-bigexprlist-vars ((x bigexprlist-p))
  :returns (vars bigvarlist-p)
  (b* (((mv seenlst ans)
        (bigexprlist-vars-memofal (bigexprlist-fix x) nil nil)))
    (fast-alist-free seenlst)
    ans)
  ///
  (defthm fast-bigexprlist-vars-elim
    (set-equiv (fast-bigexprlist-vars x)
               (bigexprlist-vars x))))
