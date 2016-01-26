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
(include-book "std/misc/two-nats-measure" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/equiv" :dir :system))
(local (include-book "tools/do-not" :dir :system))
(local (do-not generalize fertilize))

(defsection node-collect-generic-triv
  :parents (node-collect-generic)
  :short "Extended version of @(see node-collect-generic) that allows you to
avoid memoizing ``trivial'' nodes."
  :long "<p>See @(see node-collect-generic).  This is virtually identical
except that we add an extra function into the encapsulate that allows you to
say which nodes are trivial.  Trivial nodes are not recorded in the seen table
and do not contribute to the answer.</p>

<p>For example, if we are collecting variables from expressions, we shouldn't
bother recording which constants we've visited.</p>

<h3>Details and Usage</h3>

<p>The following constrained functions are similar to those in @(see
node-collect-generic) and have the same constraints:</p>

<ul>
<li>(nct-node-children node) &rarr; children</li>
<li>(nct-node-elems node) &rarr; elems</li>
<li>(nct-node-count node) &rarr; count</li>
<li>(nct-nodelist-count node) &rarr; count</li>
</ul>

<p>In addition, we add <b>(nct-node-trivial node) &rarr; bool</b> which
recognizes when a node is too trivial to bother with putting in the seen table.
We require that trivial nodes have no elements and no children.  Formally:</p>

@(def nct-node-trivial-constraint)

<h3>Spec and Implementation</h3>

<p>Trivial nodes are purely an optimization and have no effect on the logically
nice spec function:</p>

@(def nct-node-collect)
@(def nct-nodelist-collect)

<p>The implementation, however, now checks whether nodes are trivial and does
not add them to the memo table:</p>

@(def nct-node-collect-memofal)
@(def nct-nodelist-collect-memofal)

<h3>Correctness Theorems</h3>

<p>The correctness statements are unchanged:</p>

@(thm nct-node-collect-memofal-correct)
@(thm nct-nodelist-collect-memofal-correct)")

(local (xdoc::set-default-parents node-collect-generic-triv))

(encapsulate
  (((nct-node-trivial *) => *)
   ((nct-node-children *) => *)
   ((nct-node-elems *) => *)
   ((nct-node-count *) => *)
   ((nct-nodelist-count *) => *))

  (local (defun nct-node-trivial (node)
           ;; Recognizer for a node that is trivial and should not be memoized.
           (declare (ignore node))
           nil))

  (local (defun nct-node-children (node)
           ;; The children of a node.
           (if (atom node)
               nil
             (cdr node))))

  (local (defun nct-node-elems (node)
           ;; The things to collect from each node.
           (if (atom node)
               (list node)
             nil)))

  (local (mutual-recursion
          (defun nct-node-count (x)
            (declare (xargs :measure (acl2::two-nats-measure (acl2-count x) 1)))
            (+ 1 (if (nct-node-children x)
                     (nct-nodelist-count (nct-node-children x))
                   0)))
          (defun nct-nodelist-count (x)
            (declare (xargs :measure (acl2::two-nats-measure (acl2-count x) 0)))
            (if (atom x)
                0
              (+ 1
                 (nct-node-count (car x))
                 (nct-nodelist-count (cdr x)))))))

  (defthmd nct-node-trivial-constraint
    (implies (nct-node-trivial node)
             (and (not (nct-node-children node))
                  (not (nct-node-elems node)))))

  (defthmd posp-of-nct-node-count
    (posp (nct-node-count node))
    :rule-classes :type-prescription)

  (defthmd nct-nodelist-count-definition
    (equal (nct-nodelist-count nodes)
           (if (atom nodes)
               0
             (+ 1
                (nct-node-count (car nodes))
                (nct-nodelist-count (cdr nodes)))))
    :rule-classes ((:definition :controller-alist ((nct-nodelist-count t)))))

  (defthmd nct-nodelist-count-of-children-smaller
    (< (nct-nodelist-count (nct-node-children node))
       (nct-node-count node))
    :rule-classes ((:rewrite) (:linear))))

(local (in-theory (enable nct-node-trivial-constraint
                          posp-of-nct-node-count
                          nct-nodelist-count-definition
                          nct-nodelist-count-of-children-smaller)))

(local
 (defsection count-lemmas

   (defrule natp-of-nct-nodelist-count
     (natp (nct-nodelist-count nodes))
     :rule-classes :type-prescription
     :induct (len nodes)
     :enable nct-nodelist-count-definition)

   (defrule nct-nodelist-count-when-atom
     (implies (atom nodes)
              (equal (nct-nodelist-count nodes) 0))
     :enable nct-nodelist-count-definition)

   (defrule nct-nodelist-count-of-cons
     (equal (nct-nodelist-count (cons node nodes))
            (+ 1 (nct-node-count node) (nct-nodelist-count nodes)))
     :enable nct-nodelist-count-definition)

   (defrule equal-nct-nodelist-count-0
     (equal (equal (nct-nodelist-count nodes) 0)
            (atom nodes))
     :enable nct-nodelist-count-definition
     :induct (len nodes))

   (defrule nct-nodelist-count-of-cdr-strong
     (implies (consp nodes)
              (< (nct-nodelist-count (cdr nodes))
                 (nct-nodelist-count nodes)))
     :rule-classes :linear)

   (defrule nct-nodelist-count-of-cdr-weak
     (<= (nct-nodelist-count (cdr nodes))
         (nct-nodelist-count nodes))
     :rule-classes :linear)))


(defines nct-node-collect
  :verify-guards nil
  :flag-local nil
  (define nct-node-collect ((x "Root node to collect elements from."))
    :returns (elements "All transitively collected elements.")
    :short "Logically nice way (but inefficient) to collect elements from nodes."
    :measure (acl2::two-nats-measure (nct-node-count x) 1)
    (append (nct-node-elems x)
            (nct-nodelist-collect (nct-node-children x))))
  (define nct-nodelist-collect (x)
    :measure (acl2::two-nats-measure (nct-nodelist-count x) 0)
    (if (atom x)
        nil
      (append (nct-node-collect (car x))
              (nct-nodelist-collect (cdr x))))))

(defines nct-node-collect-memofal
  :verify-guards nil
  :flag-local nil
  (define nct-node-collect-memofal ((x       "Root node to collect elements from.")
                                    (seenfal "Fast alist to avoid repeating work.")
                                    (ans     "Elements we have seen so far."))
    :returns (mv (new-seenfal "Updated seen table, which has not yet been freed and
                               ought to be freed by the caller.")
                 (new-ans     "All elements that have been found in @('x'), plus
                               the original answer."))
    :short "Efficient algorithm for collecting elements from nodes."
    :measure (nct-node-count x)
    (b* (((when (nct-node-trivial x))
          ;; Trivial node, don't bother looking it up in the memo table.
          (mv seenfal ans))
         ((when (hons-get x seenfal))
          (mv seenfal ans))
         (seenfal (hons-acons x t seenfal))
         (ans     (append (nct-node-elems x) ans))
         (children (nct-node-children x))
         ((unless children)
          (mv seenfal ans)))
      (nct-nodelist-collect-memofal (nct-node-children x) seenfal ans)))
  (define nct-nodelist-collect-memofal (x seenfal ans)
    :measure (nct-nodelist-count x)
    (b* (((when (atom x))
          (mv seenfal ans))
         ((mv seenfal ans) (nct-node-collect-memofal (car x) seenfal ans)))
      (nct-nodelist-collect-memofal (cdr x) seenfal ans))))


; We will reuse the node-count proof of correctness, by simply adapting the
; definitions to account for trivial nodes.

(local
 (defsection wrappers-to-make-trivial-nodes-invisible

   (define remove-trivial-nodes (nodes)
     :verify-guards nil
     (cond ((atom nodes)
            nil)
           ((nct-node-trivial (car nodes))
            (remove-trivial-nodes (cdr nodes)))
           (t
            (cons (car nodes)
                  (remove-trivial-nodes (cdr nodes)))))
     ///
     (defthm nct-nodelist-count-of-remove-trivial-nodes
       (<= (nct-nodelist-count (remove-trivial-nodes nodes))
           (nct-nodelist-count nodes))
       :rule-classes :linear
       :hints(("Goal" :induct (len nodes)))))

   (define my-children (x)
     :verify-guards nil
     (remove-trivial-nodes (nct-node-children x)))

   (defines my-count
     :verify-guards nil
     (define my-count (x)
       :measure (nct-node-count x)
       :hints(("Goal" :in-theory (enable my-children)))
       (+ 1 (my-list-count (my-children x))))
     (define my-list-count (x)
       :measure (nct-nodelist-count x)
       :enabled t
       (if (atom x)
           0
         (+ 1
            (my-count (car x))
            (my-list-count (cdr x)))))
     ///
     (defthm posp-of-my-count
       (posp (my-count x))
       :rule-classes :type-prescription)
     (defthm natp-of-my-list-count
       (natp (my-list-count x))
       :rule-classes :type-prescription)
     (defthm my-list-count-of-my-children
       (< (my-list-count (my-children x))
          (my-count x))
       :rule-classes ((:rewrite) (:linear))))))


(local
 (defsection modified-algorithms-for-invisible-wrappers

   (defines my-collect
     :verify-guards nil
     :flag-local nil
     (define my-collect (x)
       :measure (my-count x)
       (append (nct-node-elems x)
               (my-list-collect (my-children x))))
     (define my-list-collect (x)
       :measure (my-list-count x)
       (if (atom x)
           nil
         (append (my-collect (car x))
                 (my-list-collect (cdr x))))))

   (defines my-collect-memofal
     :verify-guards nil
     :flag-local nil
     (define my-collect-memofal (x seenfal ans)
       :returns (mv new-seenfal new-ans)
       :measure (my-count x)
       (b* (((when (hons-get x seenfal))
             (mv seenfal ans))
            (seenfal (hons-acons x t seenfal))
            (ans     (append (nct-node-elems x) ans))
            (children (my-children x))
            ((unless children)
             (mv seenfal ans)))
         (my-list-collect-memofal (my-children x) seenfal ans)))
     (define my-list-collect-memofal (x seenfal ans)
       :measure (my-list-count x)
       (b* (((when (atom x))
             (mv seenfal ans))
            ((mv seenfal ans) (my-collect-memofal (car x) seenfal ans)))
         (my-list-collect-memofal (cdr x) seenfal ans))))))


; Proof that Modified Algorithms are Correct ---------------------------------

(local
 (defsection modified-algorithms-are-correct

   (local (include-book "node-collect"))

   (defthmd my-collect-memofal-correct
     (b* (((mv ?new-seenlst new-ans) (my-collect-memofal x nil ans)))
       (set-equiv new-ans (append ans (my-collect x))))
     :hints(("Goal"
             :in-theory (enable my-collect
                                my-list-collect
                                my-collect-memofal
                                my-list-collect-memofal)
             :use ((:functional-instance node-collect-memofal-correct
                    (nc-node-children         my-children)
                    (nc-node-elems            nct-node-elems)
                    (nc-node-count            my-count)
                    (nc-nodelist-count        my-list-count)
                    (node-collect             my-collect)
                    (nodelist-collect         my-list-collect)
                    (node-collect-memofal     my-collect-memofal)
                    (nodelist-collect-memofal my-list-collect-memofal))))))

   (defthmd my-list-collect-memofal-correct
     (b* (((mv ?new-seenlst new-ans) (my-list-collect-memofal x nil ans)))
       (set-equiv new-ans (append ans (my-list-collect x))))
     :hints(("Goal"
             :use ((:functional-instance nodelist-collect-memofal-correct
                    (nc-node-children         my-children)
                    (nc-node-elems            nct-node-elems)
                    (nc-node-count            my-count)
                    (nc-nodelist-count        my-list-count)
                    (node-collect             my-collect)
                    (nodelist-collect         my-list-collect)
                    (node-collect-memofal     my-collect-memofal)
                    (nodelist-collect-memofal my-list-collect-memofal))))))))

(local
 (defsection original-spec-is-modified-spec

   (local (in-theory (enable nct-node-collect
                             nct-nodelist-collect
                             my-collect
                             my-list-collect
                             my-children)))

   (defthm nct-node-collect-when-trivial
     (implies (nct-node-trivial x)
              (equal (nct-node-collect x)
                     nil)))

   (defthm nct-nodelist-collect-of-remove-trivial-nodes
     (equal (nct-nodelist-collect (remove-trivial-nodes x))
            (nct-nodelist-collect x))
     :hints(("Goal"
             :expand ((nct-nodelist-collect x)
                      (remove-trivial-nodes x))
             :in-theory (enable nct-nodelist-collect)
             :induct (len x))))

   (defthm-my-collect-flag
     (defthm nct-node-collect-is-my-collect
       (equal (nct-node-collect x)
              (my-collect x))
       :flag my-collect)
     (defthm nct-nodelist-collect-is-my-list-collect
       (equal (nct-nodelist-collect x)
              (my-list-collect x))
       :flag my-list-collect))))


(local
 (defsection original-impl-is-modified-impl

   (define remove-trivial-from-seenfal (seenfal)
     :enabled nil
     (cond ((atom seenfal)
            nil)
           ((atom (car seenfal))
            ;; Bad alist convention
            (remove-trivial-from-seenfal (cdr seenfal)))
           ((nct-node-trivial (caar seenfal))
            (remove-trivial-from-seenfal (cdr seenfal)))
           (t
            (cons (car seenfal)
                  (remove-trivial-from-seenfal (cdr seenfal)))))
     ///
     (defthm hons-assoc-equal-of-remove-trivial-from-seenfal
       (equal (hons-assoc-equal node (remove-trivial-from-seenfal seenfal))
              (if (nct-node-trivial node)
                  nil
                (hons-assoc-equal node seenfal)))))

   (local (defun my-induct (x seenfal ans)
            (b* (((when (atom x))
                  (mv seenfal ans))
                 ((mv seenfal ans) (nct-node-collect-memofal (car x) seenfal ans)))
              (my-induct (cdr x) seenfal ans))))

   (defthm nct-nodelist-collect-memofal-of-remove-trivial-nodes
     (equal (nct-nodelist-collect-memofal (remove-trivial-nodes x) seenfal ans)
            (nct-nodelist-collect-memofal x seenfal ans))
     :hints(("Goal"
             :induct (my-induct x seenfal ans)
             :expand ((nct-nodelist-collect-memofal x seenfal ans)
                      (remove-trivial-nodes x))
             :in-theory (enable nct-node-collect-memofal
                                nct-nodelist-collect-memofal))))

   (local (in-theory (enable nct-node-collect-memofal
                             nct-nodelist-collect-memofal
                             my-collect-memofal
                             my-list-collect-memofal
                             my-children)))

   (defthm nct-node-collect-memofal-when-trivial
     (implies (nct-node-trivial x)
              (equal (nct-node-collect-memofal x seenfal ans)
                     (mv seenfal ans)))
     :hints(("Goal"
             :in-theory (enable nct-node-collect-memofal)
             :expand (nct-node-collect-memofal x seenfal ans))))

   (defthm my-list-collect-memofal-when-atom
     (implies (atom x)
              (equal (my-list-collect-memofal x seenfal ans)
                     (mv seenfal ans)))
     :hints(("Goal"
             :in-theory (enable my-list-collect-memofal)
             :expand (my-list-collect-memofal x seenfal ans))))

   (defthm-nct-node-collect-memofal-flag
     (defthm nct-node-collect-memofal-is-my-collect-memofal-aux
       (b* (((mv seen1 ans1) (nct-node-collect-memofal x seenfal ans))
            ((mv seen2 ans2) (my-collect-memofal x seenfal ans)))
         (implies (not (nct-node-trivial x))
                  (and (equal seen1 seen2)
                       (equal ans1  ans2))))
       :flag nct-node-collect-memofal
       :hints('(:expand ((nct-node-collect-memofal x seenfal ans)
                         (my-collect-memofal x seenfal ans)))))
     (defthm nct-nodelist-collect-memofal-is-my-list-collect-memofal
       (b* (((mv seen1 ans1) (nct-nodelist-collect-memofal x seenfal ans))
            ((mv seen2 ans2) (my-list-collect-memofal (remove-trivial-nodes x) seenfal ans)))
         (and (equal seen1 seen2)
              (equal ans1 ans2)))
       :flag nct-nodelist-collect-memofal
       :hints('(:expand ((nct-nodelist-collect-memofal x seenfal ans)
                         (my-list-collect-memofal x seenfal ans)
                         (remove-trivial-nodes x))))))

   (defthm nct-node-collect-memofal-is-my-collect-memofal
     (b* (((mv seen1 ans1) (nct-node-collect-memofal x seenfal ans))
          ((mv seen2 ans2) (my-collect-memofal x seenfal ans)))
       (and (equal seen1 (if (nct-node-trivial x) seenfal seen2))
            (equal ans1  (if (nct-node-trivial x) ans ans2)))))))


(local (in-theory (disable set-equiv)))

(local (defthm my-collect-when-nct-node-trivial
         (implies (nct-node-trivial x)
                  (equal (my-collect x)
                         nil))
         :hints(("Goal"
                 :in-theory (enable my-collect my-children)
                 :expand (my-collect x)))))

(local (defthm my-list-collect-of-remove-trivial-nodes
         (equal (my-list-collect (remove-trivial-nodes x))
                (my-list-collect x))
         :hints(("Goal"
                 :induct (len x)
                 :expand ((my-list-collect x)
                          (:free (a x) (my-list-collect (cons a x)))
                          (remove-trivial-nodes x))))))

(defrule nct-node-collect-memofal-correct
  :short "Main correctness theorem for @(see nct-node-collect-memofal)."
  (b* (((mv ?new-seenlst new-ans) (nct-node-collect-memofal x nil ans)))
    (set-equiv new-ans (append ans (nct-node-collect x))))
  :hints(("Goal" :use ((:instance my-collect-memofal-correct)))))


(defrule nct-nodelist-collect-memofal-correct
  :short "Main correctness theorem for @(see nct-nodelist-collect-memofal)."
  (b* (((mv ?new-seenlst new-ans) (nct-nodelist-collect-memofal x nil ans)))
    (set-equiv new-ans (append ans (nct-nodelist-collect x))))
  :hints(("Goal"
          :use ((:instance my-list-collect-memofal-correct
                        (x (remove-trivial-nodes x)))))))

