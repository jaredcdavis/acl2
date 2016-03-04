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
(include-book "smallexpr")
(local (std::add-default-post-define-hook :fix))

(defines smallexpr-vars
  :parents (smallexpr)
  :short "Logically nice (but inefficient) way to collect variables from @(see
          smallexpr)s."

  (define smallexpr-vars ((x smallexpr-p))
    :returns (vars smallvarlist-p)
    :measure (smallexpr-count x)
    ;; We don't expect to ever run this.  But just in case, we put timing
    ;; messages in here so that if we ever run this by accident, we're likely
    ;; to notice it.
    (time$ (smallexpr-case x
             :const nil
             :var (list x.var)
             :call (smallexprlist-vars x.args))
           :mintime 1
           :msg "smallexpr-vars: ~st sec, ~sa bytes.~%"))

  (define smallexprlist-vars ((x smallexprlist-p))
    :parents (smallexpr-vars)
    :returns (vars smallvarlist-p)
    :measure (smallexprlist-count x)
    (if (atom x)
        nil
      (append (smallexpr-vars (car x))
              (smallexprlist-vars (cdr x)))))
  ///
  (deffixequiv-mutual smallexpr-vars))


(defines smallexpr-vars-memofal
  :parents (fast-smallexpr-vars)
  :short "Efficient algorithm for collecting elements from nodes."

  (define smallexpr-vars-memofal ((x smallexpr-p) seenfal ans)
    :returns (mv new-seenfal
                 (new-ans smallvarlist-p :hyp (smallvarlist-p ans)))
    :measure (smallexpr-count x)
    (b* ((kind (smallexpr-kind x))
         ((when (eq kind :const))
          ;; Too trivial, don't even want to mark it as seen.
          (mv seenfal ans))
         ((when (hons-get x seenfal))
          (mv seenfal ans))
         (seenfal (hons-acons x t seenfal))
         ((when (eq kind :var))
          (mv seenfal (cons (smallexpr-var->var x) ans))))
      (smallexprlist-vars-memofal (smallexpr-call->args x) seenfal ans)))

  (define smallexprlist-vars-memofal ((x smallexprlist-p) seenfal ans)
    :measure (smallexprlist-count x)
    :returns (mv new-seenfal
                 (new-ans smallvarlist-p :hyp (smallvarlist-p ans)))
    (b* (((when (atom x))
          (mv seenfal ans))
         ((mv seenfal ans) (smallexpr-vars-memofal (car x) seenfal ans)))
      (smallexprlist-vars-memofal (cdr x) seenfal ans)))

  ///
  ;; Proof of correctness using the generic node-collect-triv proof.
  ;; Almost plug-and-play, but we need a slightly modified count.

  (local (include-book "node-collect-triv"))
  (local (defines my-count
           :verify-guards nil
           (define my-count (x)
             :measure (smallexpr-count x)
             (smallexpr-case x
               :const 1
               :var 1
               :call (+ 1 (my-count-list x.args))))
           (define my-count-list (x)
             :measure (smallexprlist-count x)
             (if (atom x)
                 0
               (+ 1 (my-count (car x))
                  (my-count-list (cdr x)))))))

  (local (defthm l1
           (implies (and (not (equal (smallexpr-kind node) :const))
                         (not (equal (smallexpr-kind node) :var)))
                    (< (my-count-list (smallexpr-call->args node))
                       (my-count node)))
           :hints(("Goal" :expand ((my-count node))))))

  (local (in-theory (enable smallexpr-vars-memofal
                            smallexprlist-vars-memofal
                            smallexpr-vars
                            smallexprlist-vars
                            my-count-list)))

  (make-event
   (let ((fi-pairs
          '((nct-node-trivial             (lambda (x) (smallexpr-case x :const)))
            (nct-node-children            (lambda (x) (smallexpr-case x
                                                        :const nil
                                                        :var nil
                                                        :call x.args)))
            (nct-node-elems               (lambda (x) (smallexpr-case x
                                                        :const nil
                                                        :var (list x.var)
                                                        :call nil)))
            (nct-node-count               (lambda (x) (my-count x)))
            (nct-nodelist-count           (lambda (x) (my-count-list x)))
            (nct-node-collect             (lambda (x) (smallexpr-vars x)))
            (nct-nodelist-collect         (lambda (x) (smallexprlist-vars x)))
            (nct-node-collect-memofal     (lambda (x seen ans) (smallexpr-vars-memofal x seen ans)))
            (nct-nodelist-collect-memofal (lambda (x seen ans) (smallexprlist-vars-memofal x seen ans))))))
     `(progn
        (defthm smallexpr-vars-memofal-correct
          (b* (((mv ?new-seenlst new-ans) (smallexpr-vars-memofal x nil ans)))
            (set-equiv new-ans (append ans (smallexpr-vars x))))
          :hints(("Goal"
                  :use ((:functional-instance nct-node-collect-memofal-correct
                         . ,fi-pairs)))))

        (defthm smallexprlist-vars-memofal-correct
          (b* (((mv ?new-seenlst new-ans) (smallexprlist-vars-memofal x nil ans)))
            (set-equiv new-ans (append ans (smallexprlist-vars x))))
          :hints(("Goal"
                  :use ((:functional-instance nct-nodelist-collect-memofal-correct
                         . ,fi-pairs)))))))))

(define fast-smallexpr-vars ((x smallexpr-p))
  :returns (vars smallvarlist-p)
  (b* (((mv seenlst ans)
        (smallexpr-vars-memofal (smallexpr-fix x) nil nil)))
    (fast-alist-free seenlst)
    ans)
  ///
  (defthm fast-smallexpr-vars-elim
    (set-equiv (fast-smallexpr-vars x)
               (smallexpr-vars x))))

(define fast-smallexprlist-vars ((x smallexprlist-p))
  :returns (vars smallvarlist-p)
  (b* (((mv seenlst ans)
        (smallexprlist-vars-memofal (smallexprlist-fix x) nil nil)))
    (fast-alist-free seenlst)
    ans)
  ///
  (defthm fast-smallexprlist-vars-elim
    (set-equiv (fast-smallexprlist-vars x)
               (smallexprlist-vars x))))
