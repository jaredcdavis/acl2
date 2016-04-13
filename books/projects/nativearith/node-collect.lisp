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
(include-book "std/util/define" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "centaur/misc/equal-sets" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :system))
(local (include-book "tools/do-not" :dir :system))
(local (do-not generalize fertilize))

;; Might want to move some of these to libraries.

(local (defrule set-difference$-nil
         (equal (set-difference$ nil x)
                nil)))

(local (defrule set-difference-of-append
         (equal (set-difference$ (append x y) z)
                (append (set-difference$ x z)
                        (set-difference$ y z)))
         :induct (len x)))

(local (defrule member-when-set-equiv-to-append
         (implies (set-equiv x (append y z))
                  (iff (member k x)
                       (or (member k y)
                           (member k z))))))

(local (defrule intersection-of-append-left
         (equal (intersection$ (append a b) c)
                (append (intersection$ a c)
                        (intersection$ b c)))
         :induct (len a)))

(local (defrule intersection-of-append-right
         (set-equiv (intersection$ c (append a b))
                    (append (intersection$ c a)
                            (intersection$ c b)))
         :hints ((acl2::set-reasoning))))

(local (defthm set-equiv-append-cons-hack
         (set-equiv (append x (cons a y))
                    (cons a (append x y)))
         :hints((set-reasoning))))

(local (defthm cons-under-set-equiv-when-member
         (implies (member a x)
                  (set-equiv (cons a x)
                             x))
         :hints((set-reasoning))))


(defsection node-collect-generic
  :parents (utilities)
  :short "Reusable proof of correctness for a generic algorithm that collects
  ``elements'' from tree nodes."

  :long "<h3>Introduction</h3>

<p>Consider the goal of writing a fast function to collect variables from
honsed, heavily structure-shared terms.  In this case, we would like to
remember which nodes we have seen so that we don't recompute the variables for
subtrees that we have already visited: this will make our algorithm linear in
the size of the DAG, instead of exponential.  A good way to do that is to use a
fast alist as a seen table.</p>

<p>To avoid using lots of stack space, we'd also like to have a tail call in
the node case.  But to get that, we need to mark the node as seen <b>before</b>
we recur down to collect its childrens' variables.  But this is awful for
reasoning and really screws up the invariant about our seen table.  In
particular, the seen table now claims we have ``seen'' certain nodes that are
in a weird, partial state (because we're actually still in the process of
visiting them), so you can't just say something like: all variables for every
node we have seen are already accounted for.</p>

<p>This proof has been done time and again in the @(see aig) library, the @(see
4v) library, the @(see sv) library, etc., to introduce variable-collecting
functions.  Rather than solve it again twice more for the specific cases of,
e.g., @(see bigexpr) and @(see smallexpr) variables, we decided to abstract it
and prove the correctness of the generic algorithm.</p>

<h3>Details and Usage</h3>

<p>Note: the following scheme essentially requires that we record that
<b>all</b> nodes have been visited, even if they are trivial leaf nodes with no
elements and no children.  If you want to avoid visiting ``trivial'' nodes,
read on, but then also see @(see node-collect-generic-trivial), which extends
this basic scheme to allow for skipping nodes.</p>

<p>Our proof is about some functions that are constrained via an @(see
acl2::encapsulate).  You will need to arrange a @(see
acl2::functional-instantiation) that maps your particular tree structure to
these generic functions.</p>

<dl>

<dt>(nc-node-children node) &rarr; children</dt>
<dd>Explains how to get the children nodes for a node.</dd>

<dt>(nc-node-elems node) &rarr; elems</dt>
<dd>Extracts the desired elements to accumulate from a single node.</dd>

<dt>(nc-node-count node) &rarr; count</dt>
<dt>(nc-nodelist-count node) &rarr; count</dt>
<dd>Measures for your function to ensure termination.</dd>

</dl>

<p>We try to assume almost nothing about these functions.  In fact really the
only constraints are on the count functions.  We require:</p>

@(def posp-of-nc-node-count)
@(def nc-nodelist-count-definition)
@(def nc-nodelist-count-of-children-smaller)


<h3>Logically Nice Specification</h3>

<p>Given these constraints, we begin with the following, logically nice and
simple definition (which is of course inefficient and doesn't do anything to
avoid recomputing things):</p>

@(def node-collect)
@(def nodelist-collect)


<h3>Efficient Implementation</h3>

<p>We then implement the following ugly, but efficient, algorithm for carrying
out the same computation, which uses a fast alist as a seen table that is
updated before the recursive call (for a proper tail call), and which
accumulates its answer as it goes.</p>

@(def node-collect-memofal)
@(def nodelist-collect-memofal)


<h3>Correctness Proof</h3>

<p>The top-level correctness theorems for the implementation are provided by
the following theorems:</p>

@(thm node-collect-memofal-correct)
@(thm nodelist-collect-memofal-correct)

<p>The details of the proof are ugly and involve a creative invariant that has
been adapted from Sol Swords' proof of a similar algorithm for collecting
variables from @(see acl2::sv) expressions.</p>")

(local (xdoc::set-default-parents node-collect-generic))

; Constraints -----------------------------------------------------------------

;; Imagine something like:
;;
;; (local (mutual-recursion
;;         (defun nodep (x)
;;            (if (atom x)
;;                (integerp x)
;;              (and (symbolp (car x))
;;                   (nodelistp (cdr x)))))
;;         (defun nodelistp (x)
;;           (if (atom x)
;;               (equal x nil)
;;             (and (nodep (car x))
;;                  (nodelistp (cdr x)))))))

(encapsulate
  (((nc-node-children *) => *)
   ((nc-node-elems *) => *)
   ((nc-node-count *) => *)
   ((nc-nodelist-count *) => *))

  (local (defun nc-node-children (node)
           ;; The children of a node.
           (if (atom node)
               nil
             (cdr node))))

  (local (defun nc-node-elems (node)
           ;; The things to collect from each node
           (if (atom node)
               (list node)
             nil)))

  (local (mutual-recursion
          (defun nc-node-count (x)
            (declare (xargs :measure (acl2::two-nats-measure (acl2-count x) 1)))
            (+ 1 (if (nc-node-children x)
                     (nc-nodelist-count (nc-node-children x))
                   0)))
          (defun nc-nodelist-count (x)
            (declare (xargs :measure (acl2::two-nats-measure (acl2-count x) 0)))
            (if (atom x)
                0
              (+ 1
                 (nc-node-count (car x))
                 (nc-nodelist-count (cdr x)))))))

  (defthmd posp-of-nc-node-count
    (posp (nc-node-count node))
    :rule-classes :type-prescription)

  (defthmd nc-nodelist-count-definition
    (equal (nc-nodelist-count nodes)
           (if (atom nodes)
               0
             (+ 1
                (nc-node-count (car nodes))
                (nc-nodelist-count (cdr nodes)))))
    :rule-classes ((:definition :controller-alist ((nc-nodelist-count t)))))

  (defthmd nc-nodelist-count-of-children-smaller
    (< (nc-nodelist-count (nc-node-children node))
       (nc-node-count node))
    :rule-classes ((:rewrite) (:linear))))

(local (in-theory (enable posp-of-nc-node-count
                          nc-nodelist-count-of-children-smaller)))


(local
 (defsection count-lemmas
   ;; This is a little ugly --- we're trying not to assume very many
   ;; constraints, but, as a result, we have to prove a lot of nonsense.

   (defrule natp-of-nc-nodelist-count
     (natp (nc-nodelist-count nodes))
     :rule-classes :type-prescription
     :induct (len nodes)
     :enable nc-nodelist-count-definition)

   (defrule nc-nodelist-count-when-atom
     (implies (atom nodes)
              (equal (nc-nodelist-count nodes) 0))
     :enable nc-nodelist-count-definition)

   (defrule nc-nodelist-count-of-cons
     (equal (nc-nodelist-count (cons node nodes))
            (+ 1 (nc-node-count node) (nc-nodelist-count nodes)))
     :enable nc-nodelist-count-definition)

   (defrule equal-nc-nodelist-count-0
     (equal (equal (nc-nodelist-count nodes) 0)
            (atom nodes))
     :enable nc-nodelist-count-definition
     :induct (len nodes))

   (defrule nc-nodelist-count-of-cdr-strong
     (implies (consp nodes)
              (< (nc-nodelist-count (cdr nodes))
                 (nc-nodelist-count nodes)))
     :rule-classes :linear)

   (defrule nc-nodelist-count-of-cdr-weak
     (<= (nc-nodelist-count (cdr nodes))
         (nc-nodelist-count nodes))
     :rule-classes :linear)))


(defines node-collect
  :verify-guards nil
  :flag-local nil
  (define node-collect ((x "Root node to collect elements from."))
    :returns (elements "All transitively collected elements.")
    :short "Logically nice way (but inefficient) to collect elements from nodes."
    :measure (acl2::two-nats-measure (nc-node-count x) 1)
    (append (nc-node-elems x)
            (nodelist-collect (nc-node-children x))))
  (define nodelist-collect (x)
    :measure (acl2::two-nats-measure (nc-nodelist-count x) 0)
    (if (atom x)
        nil
      (append (node-collect (car x))
              (nodelist-collect (cdr x))))))

(defines node-collect-memofal
  :verify-guards nil
  :flag-local nil
  (define node-collect-memofal ((x       "Root node to collect elements from.")
                                (seenfal "Fast alist to avoid repeating work.")
                                (ans     "Elements we have seen so far."))
    :returns (mv (new-seenfal "Updated seen table, which has not yet been freed and
                               ought to be freed by the caller.")
                 (new-ans     "All elements that have been found in @('x'), plus
                               the original answer."))
    :short "Efficient algorithm for collecting elements from nodes."
    :measure (nc-node-count x)
    (b* (((when (hons-get x seenfal))
          (mv seenfal ans))
         (seenfal (hons-acons x t seenfal))
         (ans     (append (nc-node-elems x) ans))
         (children (nc-node-children x))
         ((unless children)
          (mv seenfal ans)))
      (nodelist-collect-memofal (nc-node-children x) seenfal ans)))
  (define nodelist-collect-memofal (x seenfal ans)
    :measure (nc-nodelist-count x)
    (b* (((when (atom x))
          (mv seenfal ans))
         ((mv seenfal ans) (node-collect-memofal (car x) seenfal ans)))
      (nodelist-collect-memofal (cdr x) seenfal ans))))

(local
 (defines node-collect-memolst
   ;; Simple version that just uses a seen list.  Main function we'll prove
   ;; correct.
   :parents nil
   :verify-guards nil
   :flag-local nil
   (define node-collect-memolst (x seenlst ans)
    :measure (nc-node-count x)
    (b* (((when (member x seenlst))
          (mv seenlst ans))
         (seenlst (cons x seenlst))
         (ans     (append (nc-node-elems x) ans))
         (children (nc-node-children x))
         ((unless children)
          (mv seenlst ans)))
      (nodelist-collect-memolst (nc-node-children x) seenlst ans)))
  (define nodelist-collect-memolst (x seenlst ans)
    :measure (nc-nodelist-count x)
    (b* (((when (atom x))
          (mv seenlst ans))
         ((mv seenlst ans) (node-collect-memolst (car x) seenlst ans)))
      (nodelist-collect-memolst (cdr x) seenlst ans)))
  ///
  (defthm-node-collect-memofal-flag
    ;; This lets us get rid of the memo table and just reason about the
    ;; seen-list version.
    (defthm remove-node-collect-memofal
      (b* (((mv new-seenfal ans-fal) (node-collect-memofal x seenfal ans))
           ((mv new-seenlst ans-lst) (node-collect-memolst x (alist-keys seenfal) ans)))
        (and (equal (alist-keys new-seenfal) new-seenlst)
             (equal ans-fal ans-lst)))
      :flag node-collect-memofal
      :hints('(:expand ((:free (seenfal ans) (node-collect-memofal x seenfal ans))
                        (:free (seenlst ans) (node-collect-memolst x seenlst ans))))))
    (defthm remove-nodelist-collect-memofal
      (b* (((mv new-seenfal ans-fal) (nodelist-collect-memofal x seenfal ans))
           ((mv new-seenlst ans-lst) (nodelist-collect-memolst x (alist-keys seenfal) ans)))
        (and (equal (alist-keys new-seenfal) new-seenlst )
             (equal ans-fal ans-lst)))
      :flag nodelist-collect-memofal
      :hints('(:expand ((:free (seenfal ans) (nodelist-collect-memofal x seenfal ans))
                        (:free (seenlst ans) (nodelist-collect-memolst x seenlst ans)))))))

  (local (flag::def-doublevar-induction double-ans-induct
           :orig-fn node-collect-memolst-flag
           :old-var ans
           :new-var ans2))

  (local (defthm-node-collect-memolst-flag
           (defthm l0
             (equal (mv-nth 0 (node-collect-memolst x seenlst ans))
                    (mv-nth 0 (node-collect-memolst x seenlst ans2)))
             :rule-classes nil
             :flag node-collect-memolst)
           (defthm l1
             (equal (mv-nth 0 (nodelist-collect-memolst x seenlst ans))
                    (mv-nth 0 (nodelist-collect-memolst x seenlst ans2)))
             :rule-classes nil
             :flag nodelist-collect-memolst)
           :hints(("Goal"
                   :induct (double-ans-induct flag x seenlst ans ans2)
                   :expand ((node-collect-memolst x seenlst ans)
                            (node-collect-memolst x seenlst ans2)
                            (nodelist-collect-memolst x seenlst ans)
                            (nodelist-collect-memolst x seenlst ans2))))))

  (defthm node-collect-memolst-canonicalize-ans
    (implies (syntaxp (not (equal ans ''nil)))
             (equal (mv-nth 0 (node-collect-memolst x seenlst ans))
                    (mv-nth 0 (node-collect-memolst x seenlst nil))))
    :hints(("Goal" :use ((:instance l0 (ans2 nil))))))

  (defthm nodelist-collect-memolst-canonicalize-ans
    (implies (syntaxp (not (equal ans ''nil)))
             (equal (mv-nth 0 (nodelist-collect-memolst x seenlst ans))
                    (mv-nth 0 (nodelist-collect-memolst x seenlst nil))))
    :hints(("Goal" :use ((:instance l1 (ans2 nil))))))

  (local (flag::def-doublevar-induction double-seenlst-induct
           :orig-fn node-collect-memolst-flag
           :old-var seenlst
           :new-var seenlst-equiv))

  (defthm-node-collect-memolst-flag
    (defthm node-collect-memolst-seenlst-congruence
      (implies (set-equiv seenlst seenlst-equiv)
               (set-equiv (mv-nth 0 (node-collect-memolst x seenlst ans))
                          (mv-nth 0 (node-collect-memolst x seenlst-equiv ans))))
      :rule-classes :congruence
      :flag node-collect-memolst)
    (defthm nodelist-collect-memolst-seenlst-congruence
      (implies (set-equiv seenlst seenlst-equiv)
               (set-equiv (mv-nth 0 (nodelist-collect-memolst x seenlst ans))
                          (mv-nth 0 (nodelist-collect-memolst x seenlst-equiv ans))))
      :rule-classes :congruence
      :flag nodelist-collect-memolst)
    :hints(("Goal"
            :induct (double-seenlst-induct flag x seenlst ans seenlst-equiv)
            :expand ((node-collect-memolst x seenlst ans)
                     (node-collect-memolst x seenlst-equiv ans)
                     (nodelist-collect-memolst x seenlst ans)
                     (nodelist-collect-memolst x seenlst-equiv ans)))))

  (defthm-node-collect-memolst-flag
    (defthm node-collect-memolst-ans-congruence
      (implies (set-equiv ans ans2)
               (set-equiv (mv-nth 1 (node-collect-memolst x seenlst ans))
                          (mv-nth 1 (node-collect-memolst x seenlst ans2))))
      :rule-classes :congruence
      :flag node-collect-memolst)
    (defthm nodelist-collect-memolst-ans-congruence
      (implies (set-equiv ans ans2)
               (set-equiv (mv-nth 1 (nodelist-collect-memolst x seenlst ans))
                          (mv-nth 1 (nodelist-collect-memolst x seenlst ans2))))
      :rule-classes :congruence
      :flag nodelist-collect-memolst)
    :hints(("Goal"
            :induct (double-ans-induct flag x seenlst ans ans2)
            :expand ((node-collect-memolst x seenlst ans)
                     (node-collect-memolst x seenlst ans2)
                     (nodelist-collect-memolst x seenlst ans)
                     (nodelist-collect-memolst x seenlst ans2)))))))


(local
 (defsection node-collect-basics

   (defrule node-collect-when-leaf
     (implies (not (nc-node-children x))
              (equal (node-collect x)
                     (acl2::list-fix (nc-node-elems x))))
     :expand ((node-collect x)))

   (defrule nodelist-collect-when-atom
     (implies (atom nodes)
              (equal (nodelist-collect nodes) nil))
     :enable nodelist-collect)

   (defrule nodelist-collect-of-cons
     (equal (nodelist-collect (cons node nodes))
            (append (node-collect node)
                    (nodelist-collect nodes)))
     :enable nodelist-collect)

   (defrule nodelist-collect-of-append
     (equal (nodelist-collect (append x y))
            (append (nodelist-collect x)
                    (nodelist-collect y)))
     :induct (len x))

   (defrule nodelist-collect-has-all-member-elements
     (implies (member node nodes)
              (subsetp (node-collect node) (nodelist-collect nodes)))
     :induct (len nodes))

   (defrule nodelist-collect-has-all-subset-elements
     (implies (subsetp x y)
              (subsetp (nodelist-collect x) (nodelist-collect y)))
     :induct (len x))

   (defcong set-equiv set-equiv (nodelist-collect nodes) 1
     :hints(("Goal" :in-theory (enable set-equiv))))

   (defrule node-collect-has-all-immediate-elements
     (subsetp-equal (nc-node-elems x) (node-collect x))
     :expand ((node-collect x)))

   (defrule node-collect-has-all-child-elements
     (implies (and (member child (nc-node-children node))
                   (member elem (node-collect child)))
              (member elem (node-collect node)))
     :rule-classes ((:rewrite)
                    (:rewrite :corollary
                     (implies (and (member elem (node-collect child))
                                   (member child (nc-node-children node)))
                              (member elem (node-collect node)))))
     :expand ((node-collect node)))

   (defrule node-collect-has-all-child-elements-2
     (implies (member child (nc-node-children node))
              (subsetp (node-collect child) (node-collect node)))
     :expand ((node-collect node)))

   (defrule node-collect-has-all-children-subset-members
     (implies (subsetp children (nc-node-children node))
              (subsetp (nodelist-collect children) (node-collect node)))
     :expand ((node-collect node)))

   (defrule member-nodelist-collect-of-intersection
     (implies (not (member elem (nodelist-collect x)))
              (not (member elem (nodelist-collect (intersection$ x y))))))

   (defrule member-nodelist-collect-of-intersection-2
     (implies (not (member elem (nodelist-collect y)))
              (not (member elem (nodelist-collect (intersection$ x y))))))))



; Why is it OK for node-collect-memolst to mark a TOP node as seen before it
; recurs into the children of TOP?  The crux is that, since there are no
; circularities, TOP must be bigger than any of its (transitive) subnodes.
; Let's explicitly define these subnodes.

(local
 (defines subnodes
   :parents nil
   :verify-guards nil
   :flag-local nil
   (define subnodes (x)
     :measure (nc-node-count x)
     (cons x (subnodes-list (nc-node-children x))))
   (define subnodes-list (x)
     :measure (nc-nodelist-count x)
     (if (atom x)
         nil
       (append (subnodes (car x))
               (subnodes-list (cdr x)))))
   ///
   (defrule subnodes-include-top
     (member node (subnodes node))
     :expand ((subnodes node)))

   (defrule subnodes-when-leaf
     (implies (not (nc-node-children x))
              (equal (subnodes x) (list x)))
     :expand ((subnodes x)))

   (defthm member-of-subnodes-when-not-member-of-children-subnodes
     (implies (not (member a (subnodes-list (nc-node-children x))))
              (iff (member a (subnodes x))
                   (equal a x)))
     :hints(("Goal" :expand ((subnodes x)))))

   (defrule subsetp-of-subnodes-list-of-nc-node-children-and-subnodes
     (subsetp (subnodes-list (nc-node-children node))
              (subnodes node))
     :expand ((subnodes node))
     :rule-classes ((:rewrite)
                    (:forward-chaining :trigger-terms ((subnodes-list (nc-node-children node))))))

   (defrule subnodes-list-when-atom
     (implies (atom nodes)
              (equal (subnodes-list nodes) nil))
     :expand ((subnodes-list nodes)))

   (defrule subnodes-list-of-cons
     (equal (subnodes-list (cons node nodes))
            (append (subnodes node) (subnodes-list nodes)))
     :expand ((subnodes-list (cons node nodes))))

   (defrule subnodes-list-of-append
     (equal (subnodes-list (append x y))
            (append (subnodes-list x) (subnodes-list y)))
     :induct (len x))

   (defthm-subnodes-flag
     (defthm member-subnodes-transitive
       (implies (and (member z (subnodes y))
                     (member y (subnodes x)))
                (member z (subnodes x)))
       :flag subnodes)
     (defthm member-subnodes-list-transitive
       (implies (and (member z (subnodes y))
                     (member y (subnodes-list x)))
                (member z (subnodes-list x)))
       :flag subnodes-list))

   (defthm-subnodes-flag
     (defthm not-member-of-subnodes-by-count
       (implies (< (nc-node-count x) (nc-node-count y))
                (not (member y (subnodes x))))
       :flag subnodes)
     (defthm not-member-of-subnodes-list-by-count
       (implies (< (nc-nodelist-count x) (nc-node-count y))
                (not (member y (subnodes-list x))))
       :flag subnodes-list))

   (defthm-subnodes-flag
     (defthm member-var-of-subnodes-transitive
       (implies (and (member elem (node-collect y))
                     (member y (subnodes x)))
                (member elem (node-collect x)))
       :hints ('(:expand ((node-collect x)
                          (subnodes x))))
       :flag subnodes)
     (defthm member-var-of-subnodes-list-transitive
       (implies (and (member elem (node-collect y))
                     (member y (subnodes-list x)))
                (member elem (nodelist-collect x)))
       :hints ('(:expand ((nodelist-collect x)
                          (subnodes-list x))))
       :flag subnodes-list))

   (defthm-subnodes-flag
     (defthm nodelist-collect-of-subnodes
       (set-equiv (nodelist-collect (subnodes x))
                  (node-collect x))
       :hints ('(:expand ((subnodes x)
                          (node-collect x)
                          (:free (a b) (nodelist-collect (cons a b))))))
       :flag subnodes)
     (defthm nodelist-collect-of-subnodes-list
       (set-equiv (nodelist-collect (subnodes-list x))
                  (nodelist-collect x))
       :hints ('(:expand ((subnodes-list x)
                          (nodelist-collect x))))
       :flag subnodes-list))))


; We can now show that, even though node-collect-memolst marks the current node
; before recurring, by the time it returns it has marked all subnodes.  This is
; the nastiest, hardest to get your head around part of the proof.

(local
 (defsection seen-list-invariant

   (defquant node-inv (node seenlst)
     (forall (sub z)
             (implies (and (member sub (subnodes node))
                           (member sub seenlst)
                           (member z (subnodes sub)))
                      (member z seenlst)))
     :rewrite :direct)

   (defquant nodelist-inv (node seenlst)
     (forall (sub z)
             (implies (and (member sub (subnodes-list node))
                           (member sub seenlst)
                           (member z (subnodes sub)))
                      (member z seenlst)))
     :rewrite :direct)

   (defexample node-inv-example
     :pattern (member z (subnodes sub))
     :templates (sub z)
     :instance-rulename node-inv-instancing)

   (defexample nodelist-inv-example
     :pattern (member z (subnodes sub))
     :templates (sub z)
     :instance-rulename nodelist-inv-instancing)

   (defrule nodelist-inv-of-children
     (implies (node-inv node seenlst)
              (nodelist-inv (nc-node-children node) seenlst))
     :hints (("Goal"
              :expand ((subnodes node))
              :in-theory (enable node-inv-necc))
             (witness)))

   (defrule node-inv-of-car
     (implies (and (nodelist-inv nodes seenlst)
                   (consp nodes))
              (node-inv (car nodes) seenlst))
     :hints (("Goal"
              :expand ((subnodes-list nodes))
              :in-theory (enable nodelist-inv-necc))
             (witness)))

   (defrule nodelist-inv-of-cdr
     (implies (nodelist-inv nodes seenlst)
              (nodelist-inv (cdr nodes) seenlst))
     :hints (("goal"
              :expand ((subnodes-list nodes))
              :in-theory (enable nodelist-inv-necc))
             (witness)))

   (defrule node-inv-initial
     (node-inv node nil)
     :hints ((witness)))

   (defrule nodelist-inv-initial
     (nodelist-inv nodes nil)
     :hints ((witness)))

   ;; Powerful rules: (subnodes y) produces a complete list of all subnodes, so
   ;; it's a valid seen table for any X even if X is unrelated to Y.

   (defrule node-inv-of-subnodes
     (node-inv x (subnodes y))
     :hints ((witness)))

   (defrule nodelist-inv-of-subnodes
     (nodelist-inv x (subnodes y))
     :hints ((witness)))

   (defrule node-inv-of-subnodes-list
     (node-inv x (subnodes-list y))
     :hints ((witness)))

   (defrule nodelist-inv-of-subnodes-list
     (nodelist-inv x (subnodes-list y))
     :hints ((witness)))

   (defexample node-inv-example-args
     :pattern (member z (subnodes-list (nc-node-children sub)))
     :templates (sub z)
     :instance-rulename node-inv-instancing)

   (defsection node-inv-congruence

     (local (defthmd l0
              (implies (and (node-inv node seenlst)
                            (set-equiv seenlst seenlst2))
                       (node-inv node seenlst2))
              :hints((witness))))

     (local (defthmd l1
              (implies (and (not (node-inv node seenlst))
                            (set-equiv seenlst seenlst2))
                       (not (node-inv node seenlst2)))
              :hints((witness))))

     (defcong set-equiv equal (node-inv node seenlst) 2
       :hints(("Goal" :use ((:instance l0 (seenlst seenlst) (seenlst2 acl2::seenlst-equiv))
                            (:instance l1 (seenlst seenlst) (seenlst2 acl2::seenlst-equiv)))))))

   (defsection nodelist-inv-congruence

     (local (defthmd l0
              (implies (and (nodelist-inv node seenlst)
                            (set-equiv seenlst seenlst2))
                       (nodelist-inv node seenlst2))
              :hints((witness))))

     (local (defthmd l1
              (implies (and (not (nodelist-inv node seenlst))
                            (set-equiv seenlst seenlst2))
                       (not (nodelist-inv node seenlst2)))
              :hints((witness))))

     (defcong set-equiv equal (nodelist-inv node seenlst) 2
       :hints(("Goal" :use ((:instance l0 (seenlst seenlst) (seenlst2 acl2::seenlst-equiv))
                            (:instance l1 (seenlst seenlst) (seenlst2 acl2::seenlst-equiv)))))))


   (defsection seenlist-correct

     (local (defthm l0
              (implies (and (member-equal x seenlst)
                            (node-inv x seenlst))
                       (subsetp-equal (subnodes-list (nc-node-children x)) seenlst))
              :hints((witness))))

     (local (defthm l1
              (implies (node-inv x seenlst)
                       (nodelist-inv (nc-node-children x) (cons x seenlst)))
              :hints((witness))))

     (local (defthm l2
              (implies (and (nodelist-inv x seenlst)
                            (nodelist-inv x y))
                       (nodelist-inv x (append seenlst y)))
              :hints((witness))))

     (defthm-node-collect-memolst-flag
       (defthm node-collect-memolst-seen-correct
         (b* (((mv new-seenlst ?new-ans) (node-collect-memolst x seenlst ans)))
           (implies (node-inv x seenlst)
                    (set-equiv new-seenlst (append (subnodes x) seenlst))))
         :flag node-collect-memolst
         :hints ('(:expand ((node-collect-memolst x seenlst ans)
                            (subnodes x))
                   :in-theory (enable node-inv-necc))))
       (defthm nodelst-collect-memolst-seen-correct
         (b* (((mv new-seenlst ?new-ans) (nodelist-collect-memolst x seenlst ans)))
           (implies (nodelist-inv x seenlst)
                    (set-equiv new-seenlst (append (subnodes-list x) seenlst))))
         :flag nodelist-collect-memolst
         :hints ('(:expand ((nodelist-collect-memolst x seenlst ans)
                            (subnodes-list x))
                   :in-theory (enable nodelist-inv-necc))))))

   (defrule node-collect-memo-preserves-inv
     (b* (((mv new-seenlst ?new-ans) (node-collect-memolst x seenlst ans)))
       (implies (and (node-inv y seenlst)
                     (node-inv x seenlst))
                (node-inv y new-seenlst)))
     :hints (("Goal" :in-theory (enable node-inv-necc))
             (witness :ruleset node-inv-witnessing)))

   (defrule node-collect-memo-preserves-seenlist-invariant
     (b* (((mv new-seenlst ?new-ans) (node-collect-memolst x seenlst ans)))
       (implies (and (nodelist-inv y seenlst)
                     (node-inv x seenlst))
                (nodelist-inv y new-seenlst)))
     :hints (("Goal" :in-theory (enable nodelist-inv-necc))
             (witness :ruleset nodelist-inv-witnessing)))

   (defrule nodelist-collect-memo-preserves-inv
     (b* (((mv new-seenlst ?new-ans) (nodelist-collect-memolst x seenlst ans)))
       (implies (and (node-inv y seenlst)
                     (nodelist-inv x seenlst))
                (node-inv y new-seenlst)))
     :hints (("Goal" :in-theory (enable node-inv-necc))
             (witness :ruleset node-inv-witnessing)))

   (defrule nodelist-collect-memo-preserves-seenlist-list-invar
     (b* (((mv new-seenlst &) (nodelist-collect-memolst x seenlst ans)))
       (implies (and (nodelist-inv y seenlst)
                     (nodelist-inv x seenlst))
                (nodelist-inv y new-seenlst)))
     :hints (("Goal" :in-theory (enable nodelist-inv-necc))
             (witness :ruleset nodelist-inv-witnessing)))))


; The correctness of the answer is much simpler, and here's a really nice trick
; that lets us show it is correct without needing another complicated
; invariant.  Instead of showing any relationship between X and ANS, we'll just
; show that the answer contains all the elements for all the nodes in the seen
; list.

(local
 (define seenlist-elems (seenlst)
   :parents nil
   :verify-guards nil
   (if (atom seenlst)
       nil
     (append (nc-node-elems (car seenlst))
             (seenlist-elems (cdr seenlst))))
   ///
   (defthm seenlist-elems-when-atom
     (implies (atom seenlst)
              (equal (seenlist-elems seenlst)
                     nil)))

   (defthm seenlist-elems-of-cons
     (equal (seenlist-elems (cons a x))
            (append (nc-node-elems a)
                    (seenlist-elems x))))

   (defthm seenlist-elems-of-append
     (equal (seenlist-elems (append x y))
            (append (seenlist-elems x)
                    (seenlist-elems y))))

   (defthm nc-node-elems-in-seenlist-elems-when-member
     (implies (member a x)
              (subsetp (nc-node-elems a) (seenlist-elems x)))
     :hints(("Goal" :induct (len x))))

   (defthm seenlist-elems-when-subset
     (implies (subsetp x y)
              (subsetp (seenlist-elems x) (seenlist-elems y)))
     :hints(("Goal" :induct (len x))))

   (defcong set-equiv set-equiv (seenlist-elems seenlst) 1
     :hints(("Goal" :in-theory (enable set-equiv))))

   (defthm-node-collect-flag
     ;; Beautiful theorem translating the spec function into a flat alternative.
     (defthmd node-collect-is-seenlist-elems
       (set-equiv (node-collect x)
                  (seenlist-elems (subnodes x)))
       :flag node-collect
       :hints('(:expand ((node-collect x)
                         (subnodes x)))))
     (defthmd nodelist-collect-is-seenlist-elems
       (set-equiv (nodelist-collect x)
                  (seenlist-elems (subnodes-list x)))
       :flag nodelist-collect))

   (defthm-node-collect-memolst-flag
     ;; If you consider just the special case where extra is NIL, we're
     ;; showing
     ;;
     ;;      (set-equiv ans (seenlist-elems seenlst))
     ;;         -->
     ;;      (set-equiv new-ans (seenlist-elems new-seenlst))
     ;;
     ;; We include "extra" only so that when we go to use this theorem below,
     ;; we can account precisely for any initial values in ans that aren't part
     ;; of the nodes that we are visiting.
     (defthm node-collect-memolst-sees-everything
       (b* (((mv new-seenlst new-ans) (node-collect-memolst x seenlst ans)))
         (implies (set-equiv ans     (append extra (seenlist-elems seenlst)))
                  (set-equiv new-ans (append extra (seenlist-elems new-seenlst)))))
       :flag node-collect-memolst
       :hints ('(:expand ((node-collect-memolst x seenlst ans)))
               (set-reasoning)))
     (defthm nodelist-collect-memolst-sees-everything
       (b* (((mv new-seenlst new-ans) (nodelist-collect-memolst x seenlst ans)))
         (implies (set-equiv ans     (append extra (seenlist-elems seenlst)))
                  (set-equiv new-ans (append extra (seenlist-elems new-seenlst)))))
       :flag nodelist-collect-memolst
       :hints ('(:expand ((nodelist-collect-memolst x seenlst ans))))))))


(local
 (defsection node-collect-memolst-correct

   (defthmd node-collect-memolst-correct-crux
     ;; Proof sketch:
     ;;
     ;; Using NODE-COLLECT-MEMOLST-SEES-EVERYTHING, the set-equiv hyp gives:
     ;;
     ;;        new-ans === (append extra (seenlist-elems new-seenlst))
     ;;
     ;; Using NODE-COLLECT-MEMOLST-SEEN-CORRECT, and the node-inv hyp, we get:
     ;;
     ;;        new-seenlst === (append (subnodes x) seenlst)
     ;;
     ;; Equality substitution of the above gives:
     ;;
     ;;        new-ans === (append extra (seenlist-elems (append (subnodes x) seenlst)))
     ;;
     ;; By seenlist-elems-of-append we get:
     ;;
     ;;        new-ans === (append extra (seenlist-elems (subnodes x)) (seenlist-elems seenlst))))
     ;;
     ;; Finally by NODE-COLLECT-IS-SEENLIST-ELEMS the (seenlist-elems (subnodes x))
     ;; turns into (node-collect x).
     (b* (((mv ?new-seenlst new-ans) (node-collect-memolst x seenlst ans)))
       (implies (and (node-inv x seenlst)
                     (set-equiv ans (append extra (seenlist-elems seenlst))))
                (set-equiv new-ans (append extra (seenlist-elems seenlst)
                                           (node-collect x)))))
     :hints(("goal" :in-theory (enable node-collect-is-seenlist-elems))))

   (defthmd nodelist-collect-memolst-correct-crux
     (b* (((mv ?new-seenlst new-ans) (nodelist-collect-memolst x seenlst ans)))
       (implies (and (nodelist-inv x seenlst)
                     (set-equiv ans (append extra (seenlist-elems seenlst))))
                (set-equiv new-ans (append extra (seenlist-elems seenlst)
                                           (nodelist-collect x)))))
     :hints(("goal" :in-theory (enable nodelist-collect-is-seenlist-elems))))

   ;; Nice versions: just drop the seenlst and the invariant evaporates...

   (defrule node-collect-memolst-correct
     (b* (((mv ?new-seenlst new-ans) (node-collect-memolst x nil ans)))
       (set-equiv new-ans (append ans (node-collect x))))
     :use ((:instance node-collect-memolst-correct-crux
            (seenlst nil)
            (extra ans))))

   (defrule nodelist-collect-memolst-correct
     (b* (((mv ?new-seenlst new-ans) (nodelist-collect-memolst x nil ans)))
       (set-equiv new-ans (append ans (nodelist-collect x))))
     :use ((:instance nodelist-collect-memolst-correct-crux
            (seenlst nil)
            (extra ans))))))


;; The correctness of the fast-alist version then follows basically directly from
;; the above along with REMOVE-NODE-COLLECT-MEMOFAL.

(defrule node-collect-memofal-correct
  :short "Main correctness theorem for @(see node-collect-memofal)."
  (b* (((mv ?new-seenlst new-ans) (node-collect-memofal x nil ans)))
    (set-equiv new-ans (append ans (node-collect x)))))

(defrule nodelist-collect-memofal-correct
  :short "Main correctness theorem for @(see nodelist-collect-memofal)."
  (b* (((mv ?new-seenlst new-ans) (nodelist-collect-memofal x nil ans)))
    (set-equiv new-ans (append ans (nodelist-collect x)))))
