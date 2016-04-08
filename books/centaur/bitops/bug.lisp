;; Bug?  Slow array access

(in-package "BITOPS")
(include-book "tools/rulesets" :dir :system)
(include-book "centaur/misc/context-rw" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "ihsext-basics")
(local (include-book "ihs-extensions"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "equal-by-logbitp"))

; Added by Matt K., 7/2014: disable waterfall parallelism for the proofs below,
; since some call logbitp-reasoning.  See the long comment near the form
; (non-parallel-book) in centaur/bitops/equal-by-logbitp.lisp.

(local (include-book "std/system/non-parallel-book" :dir :system))
(local (non-parallel-book)) ; probably need not be local

(defmacro def-context-rule (name body &rest args)
  (let* ((fnname-look (ec-call (assoc-keyword :fnname args)))
         (fnname (cadr fnname-look))
         (rest-args (append (take (- (len args) (len fnname-look)) args)
                            (cddr fnname-look))))
    `(progn (defthmd ,name ,body . ,rest-args)
            (add-context-rule ,fnname (:rewrite ,name)))))



;; Since we're normalizing to logsquash of loghead, propagate a logsquash
;; context inside loghead:
;; This is its own removal rule.
(def-context-rule logsquash-of-loghead-context
  (equal (logsquash n (loghead m (logsquash n x)))
         (logsquash n (loghead m x)))
  :fnname logsquash$inline)
(in-theory (disable apply-context-for-logsquash$inline))

(in-theory (enable logsquash-of-loghead-context))

;; ;; Logbitp induces both a logsquash and loghead context.
;; (defthm logbitp-remove-logsquash
;;   (implies (<= (nfix m) (nfix n))
;;            (equal (logbitp n (logsquash m i))
;;                   (logbitp n i))))

;; (defthm logbitp-remove-loghead
;;   (implies (< (nfix n) (nfix m))
;;            (equal (logbitp n (loghead m i))
;;                   (logbitp n i))))

;; Removal rule: logbitp-of-logsquash-in-bounds
(def-context-rule logbitp-induces-logsquash/loghead-context
  (implies (syntaxp (not (quotep n)))
           ;; if n is quotep we'll prefer a logand context instead
           (equal (logbitp n (logsquash n (loghead (+ 1 (nfix n)) i)))
                  (logbitp n i)))
  :fnname logbitp)

(in-theory (disable common-lisp::apply-context-for-logbitp))

;; ;; Logtail induces a logsquash context.
;; It also passes a (modified) loghead context.

;; Removal rule: logtail-of-logsquash
(def-context-rule logtail-induces-logsquash-context
  (equal (logtail n (logsquash n i))
         (logtail n i))
  :fnname acl2::logtail$inline)

(in-theory (disable acl2::apply-context-for-logtail$inline))

;; Removal rule: logtail-of-loghead
(def-context-rule logtail-pass-loghead-context
  (equal (loghead n (logtail m (loghead (+ (nfix n) (nfix m)) i)))
         (loghead n (logtail m i)))
  :hints(("Goal" :in-theory (disable logsquash)))
  :fnname acl2::loghead$inline)

(in-theory (disable acl2::apply-context-for-loghead$inline))


;; Logic ops are transparent to both types of context.

;; Logior:
(defthm logior-remove-loghead-1
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logior (loghead m a) b))
                  (loghead n (logior a b)))))

(def-context-rule logior-pass-loghead-context-1
  (equal (loghead n (logior (loghead n a) b))
         (loghead n (logior a b)))
  :fnname acl2::loghead$inline)

(defthm logior-remove-loghead-2
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logior a (loghead m b)))
                  (loghead n (logior a b)))))

(def-context-rule logior-pass-loghead-context-2
  (equal (loghead n (logior a (loghead n b)))
         (loghead n (logior a b)))
  :fnname acl2::loghead$inline)

(defthm logior-remove-logsquash-1
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logior (logsquash m a) b))
                  (logsquash n (logior a b))))
  :hints ((logbitp-reasoning)))

(defthm logior-remove-logsquash-2
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logior a (logsquash m b)))
                  (logsquash n (logior a b))))
  :hints ((logbitp-reasoning)))

(def-context-rule logior-pass-logsquash-context-1
  (equal (logsquash n (logior (logsquash n a) b))
         (logsquash n (logior a b)))
  :fnname logsquash$inline)

(def-context-rule logior-pass-logsquash-context-2
  (equal (logsquash n (logior a (logsquash n b)))
         (logsquash n (logior a b)))
  :fnname logsquash$inline)

;; Logand:
(defthm logand-remove-loghead-1
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logand (loghead m a) b))
                  (loghead n (logand a b)))))

(defthm logand-remove-loghead-2
  (implies (<= (nfix n) (nfix m))
           (equal (loghead n (logand a (loghead m b)))
                  (loghead n (logand a b)))))

(def-context-rule logand-pass-loghead-context-1
  (equal (loghead n (logand (loghead n a) b))
         (loghead n (logand a b)))
  :fnname acl2::loghead$inline)

(def-context-rule logand-pass-loghead-context-2
  (equal (loghead n (logand a (loghead n b)))
         (loghead n (logand a b)))
  :fnname acl2::loghead$inline)

(local (set-default-hints
        '((logbitp-reasoning)
          (and stable-under-simplificationp
               '(:in-theory (enable b-ior b-and b-not b-xor
                                    nfix))))))

(defthm logand-remove-logsquash-1
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logand (logsquash m a) b))
                  (logsquash n (logand a b)))))

(defthm logand-remove-logsquash-2
  (implies (<= (nfix m) (nfix n))
           (equal (logsquash n (logand a (logsquash m b)))
                  (logsquash n (logand a b)))))

(def-context-rule logand-pass-logsquash-context-1
  (equal (logsquash n (logand (logsquash n a) b))
         (logsquash n (logand a b)))
  :fnname logsquash$inline)

(def-context-rule logand-pass-logsquash-context-2
  (equal (logsquash n (logand a (logsquash n b)))
         (logsquash n (logand a b)))
  :fnname logsquash$inline)




;; Addition/subtraction pass loghead, but not logsquash, contexts

(local
 (encapsulate
   nil
   (local (defun ind (n m a b c)
            (if (zp n)
                (list m a b c)
              (ind (1- n) (1- m)
                   (logcdr a)
                   (logcdr b)
                   (b-ior (b-and (logcar a) (logcar b))
                          (b-ior
                           (b-and (logcar a) (logcar c))
                           (b-and (logcar b) (logcar c))))))))


; Reordering the rewrite-clause-type-alist: I added the uppercase text below to
; make this work.  See the comment in rewrite-clause-type-alist.
; JSM April 7, 2013.

   (defthm loghead-of-sum-lemma
     (implies (and (integerp a)
                   (integerp b)
                   (bitp c)
                   (<= (nfix n) (nfix m)))
              (equal (loghead n (+ c a (loghead m b)))
                     (loghead n (+ c a b))))
     :hints (("goal"
              :induct (ind n m a b c)
              :do-not '(generalize fertilize)
              :expand ((:free (b) (loghead n b))
                       (:free (b) (loghead m b)))
              :in-theory (e/d (nfix logcdr-of-bit b-and b-ior b-not)
                              (loghead-identity
                               (:FORWARD-CHAINING LOGCAR-POSSIBILITIES)
                               ))
              :do-not-induct t))
     :rule-classes nil)))

