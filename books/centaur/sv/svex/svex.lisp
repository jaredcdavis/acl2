; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "SV")
(include-book "4vec-base")
(include-book "std/lists/repeat" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :system))

(defflexsum svar
  :parents (svex)
  :kind nil
  (:svar
   :short "A single variable in a symbolic vector expression."
   :type-name svar
   :cond t
   :shape (if (atom x)
              (or (stringp x)
                  (and (symbolp x)
                       (not (booleanp x))))
            (and (eq (car x) :var)
                 (consp (cdr x))
                 (not (and (or (stringp (cadr x))
                               (and (symbolp (cadr x))
                                    (not (booleanp (cadr x)))))
                           (eql (cddr x) 0)))))
   :fields
   ((name :acc-body (if (atom x)
                        x
                      (cadr x))
          :doc "The name of this variable.  This can be any ACL2 object at all,
                but our representation is optimized for @(see stringp) or @(see
                symbolp) names.")
    (delay :type natp
           :acc-body (if (atom x) 0 (cddr x))
           :default 0
           :doc "An natural valued index for this variable, used for instance
                 to support the encoding of, e.g., previous versus current
                 register values in FSMs.  The default delay (which enjoys an
                 optimized representation) is 0.  See below for some motivation
                 and explanation."))
   :ctor-body
   (if (and (or (stringp name)
                (and (symbolp name)
                     (not (booleanp name))))
            (eql delay 0))
       name
     (hons :var (hons name delay)))
   :long "<p>Each variable in an @(see svex) represents a @(see 4vec).</p>

<p>In most s-expression formats, e.g., s-expressions in Lisp or in the @(see
acl2::4v-sexprs) used in @(see acl2::esim), a variable is just a symbol, which
is generally treated as if it were an atomic <b>name</b> with no further
structure.</p>

<p>In contrast, in @(see sv), our variables have both a name and also a natural
numbered index (called @('delay')).  This index is mainly an implementation
detail that allows us to cheaply (i.e., without @(see intern$)) construct new
variables.</p>

<p>In the semantics of expressions, e.g., in @(see svex-lookup), variables are
distinct whenever they differ by name <b>or</b> by delay.  That is, as far as
expression evaluation is concerned, the variable named \"v\" with delay 5 is
completely distinct from \"v\" with delay 4.  Think of them as you would
indexed variables like @($v_5$) versus @($v_4$) in some mathematics.</p>"))

(deflist svarlist
  :elt-type svar
  :true-listp t
  :elementp-of-nil nil
  :parents (svar)
  ///
  (local (defun svar-member (k x)
           (if (atom x)
               nil
             (if (equal (svar-fix (car x)) k)
                 (car x)
               (svar-member k (cdr x))))))

  (local (defthm witness-member-svarlist-fix
           (implies (and (equal k (svar-fix v))
                         (member v x))
                    (member k (svarlist-fix x)))
           :hints(("Goal" :in-theory (enable svarlist-fix)))))

  (local (defthm member-svarlist-fix
           (implies (acl2::rewriting-negative-literal `(member-equal ,k (svarlist-fix$inline ,x)))
                    (iff (member k (svarlist-fix x))
                         (and (equal k (svar-fix (svar-member k x)))
                              (member (svar-member k x) x))))
           :hints(("Goal" :in-theory (enable svarlist-fix)))))

  (defcong set-equiv set-equiv (svarlist-fix x) 1
    :hints ((acl2::witness :ruleset acl2::set-equiv-witnessing))))


(defalist svar-alist
  :key-type svar
  :parents (svar))

(defalist svar-map
  :key-type svar
  :val-type svar
  :parents (svar))


(defxdoc fnsym
  :parents (svex)
  :short "A valid function name in an @(see svex) expressions."
  :long "<p>Syntactically, we allow most symbols to be used as function names.
However, our expression language is fixed: only a few certain pre-defined
function symbols like @('bitnot'), @('concat'), etc., are understood by
functions like @(see svex-eval) and user-defined functions are not supported.
See @(see svex-functions) for details.</p>")

(define fnsym-p (x)
  :parents (fnsym)
  :short "Recognizer for valid @(see fnsym)s."
  (and (symbolp x)
       (not (eq x 'quote))
       (not (keywordp x)))
  ///
  (defthm fnsym-p-compound-recognizer
    (implies (fnsym-p x)
             (symbolp x))
    :rule-classes :compound-recognizer))

(define fnsym-fix (x)
  :parents (fnsym)
  :short "Fixing function for @(see fnsym)s."
  :returns (x fnsym-p)
  (if (fnsym-p x)
      x
    'id)
  ///
  (defthm fnsym-fix-when-fnsym-p
    (implies (fnsym-p x)
             (equal (fnsym-fix x) x))))

(defsection fnsym-equiv
  :parents (fnsym)
  :short "Equivalence relation for @(see fnsym)s."
  (deffixtype fnsym
    :pred fnsym-p
    :fix fnsym-fix
    :equiv fnsym-equiv
    :define t
    :forward t
    :equal eq))


(deftypes svex
  :parents (expressions)
  :short "Our core expression data type.  A <b>S</b>ymbolic <b>V</b>ector
<b>Ex</b>pression may be either a constant @(see 4vec), a <see topic='@(url
svar)'>variable</see>, or a function applied to subexpressions."

  :long "<p>See @(see expressions) for background.  Each svex represents a
single @(see 4vec) result.  The semantics are given by @(see svex-eval).</p>

<p>Our @(see svex) expressions are always created with @(see hons) for
automatic structure sharing.  Most operations over these expressions should
typically be @(see memoize)d in some way or another.</p>"
  :prepwork ((local (defthm 4vec-not-svar-p
                      (implies (svar-p x)
                               (not (4vec-p x)))
                      :hints(("Goal" :in-theory (enable 4vec-p svar-p)))))
             (local (defthm cons-fnsym-not-svar-p
                      (implies (not (eq x :var))
                               (not (svar-p (cons x y))))
                      :hints(("Goal" :in-theory (enable fnsym-p svar-p))))))
  (defflexsum svex
    (:var
     :short "A variable, which represents a @(see 4vec)."
     :cond (svar-p x)
     :fields ((name :acc-body x :type svar-p))
     :ctor-body name)
    (:quote
     :short "A ``quoted constant'' @(see 4vec), which represents itself."
     :cond (or (atom x)
               (eq (car x) 'quote))
     :shape (or (atom x) (and (consp (cdr x))
                              (consp (cadr x))
                              (not (cddr x))))
     :fields ((val :acc-body (if (atom x) x (cadr x))
                   :type 4vec))
     :ctor-body (if (atom val) val (hons 'quote (hons val nil))))
    (:call
     :short "A function applied to some expressions."
     :cond t
     :fields ((fn :acc-body (car x)
                  :type fnsym)
              (args :acc-body (cdr x)
                    :type svexlist))
     :ctor-body (hons fn args)))
  (deflist svexlist
    :elt-type svex
    :true-listp t))

(memoize 'svex-p :condition '(consp x))

(defsection svex-x
  :parents (svex)
  :short "An @(see svex) constant for an infinite-width X."
  :long "@(def *svex-x*) @(def svex-x)"
  (defconst *svex-x* (svex-quote (4vec-x)))
  (defmacro svex-x () `',*svex-x*))

(defsection svex-z
  :parents (svex)
  :short "An @(see svex) constant for an infinite-width X."
  :long "@(def *svex-z*) @(def svex-z)"
  (defconst *svex-z* (svex-quote (4vec-z)))
  (defmacro svex-z () `',*svex-z*))

(defsection svex-1x
  :parents (svex)
  :short "An @(see svex) constant for an single X bit (lsb), upper bits all 0."
  :long "@(def *svex-1x*) @(def svex-1x)"
  (defconst *svex-1x* (svex-quote (4vec-1x)))
  (defmacro svex-1x () `',*svex-1x*))

(defsection svex-1z
  :parents (svex)
  :short "An @(see svex) constant for an single X bit (lsb), upper bits all 0."
  :long "@(def *svex-1z*) @(def svex-1z)"
  (defconst *svex-1z* (svex-quote (4vec-1z)))
  (defmacro svex-1z () `',*svex-1z*))

(defthm len-of-svexlist-fix
  (equal (len (svexlist-fix x))
         (len x)))

(defthm svex-count-of-car-weak
  (<= (svex-count (car args))
      (svexlist-count args))
  :hints (("goal" :cases ((consp args))))
  :rule-classes :linear)

(defthm svexlist-count-of-cdr-weak
  (<= (svexlist-count (cdr args))
      (svexlist-count args))
  :hints (("goal" :cases ((consp args))))
  :rule-classes :linear)

(defcong svexlist-equiv svex-equiv (nth n x) 2
  :hints(("Goal" :in-theory (enable svexlist-equiv svex-equiv svexlist-fix)
          :induct (svex-equiv (nth n x) (nth n x-equiv))
          :expand ((svexlist-fix x) (svexlist-fix x-equiv)))))


(define svex-nth ((n natp) (x svexlist-p))
  :parents (svexlist)
  :returns (expr svex-p)
  :short "@(see nth) for @(see svexlist)s, with proper @(see fty-discipline)."
  :enabled t
  :guard-debug t
  (mbe :logic (svex-fix (nth n x))
       :exec (if (< n (len x))
                 (nth n x)
               (svex-quote (4vec-x)))))

(define svex-update-nth ((n natp) (v svex-p) (x svexlist-p))
  :parents (svexlist)
  :short "@(see update-nth) for @(see svexlist)s, with proper @(see fty-discipline)."
  :enabled t
  :returns (new-x svexlist-p)
  :prepwork ((local (in-theory (e/d (update-nth replicate svexlist-fix)
                                    (acl2::equal-of-append-repeat))))
             (local (include-book "arithmetic/top-with-meta" :dir :system)))
  (mbe :logic (svexlist-fix (update-nth n v x))
       :exec (if (<= n (len x))
                 (update-nth n v x)
               (append x
                       (replicate (- n (len x)) (svex-quote (4vec-x)))
                       (list v)))))

(defalist svex-alist
  :key-type svar
  :val-type svex
  :true-listp t
  :parents (svex)
  :short "Alist binding variables (@(see svar)s) to expressions @(see svex)es."
  ///
  (defthm svex-alist-p-of-pairlis$
    (implies (and (svarlist-p x)
                  (svexlist-p y)
                  (equal (len x) (len y)))
             (svex-alist-p (pairlis$ x y)))
    :hints(("Goal" :in-theory (enable svex-alist-p
                                      svarlist-p
                                      svexlist-p)))))




(define svex-acons ((var svar-p) (v svex-p) (a svex-alist-p))
  :parents (svex-alist)
  :short "Like @(see acons), but with proper @(see fty-discipline) for @(see svex-alist)s."
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p))))
  :returns (aa svex-alist-p)
  (mbe :logic (cons (cons (svar-fix var)
                          (svex-fix v))
                    (svex-alist-fix a))
       :exec (cons (cons var v) a))
  ///
  (deffixequiv svex-acons))


(define svex-fastacons ((var svar-p) (v svex-p) (a svex-alist-p))
  :parents (svex-alist)
  :short "Like @(see hons-acons), but with proper @(see fty-discipline) for @(see svex-alist)s."
  :prepwork ((local (in-theory (enable svex-acons))))
  :enabled t
  :inline t
  (mbe :logic (svex-acons var v a)
       :exec (hons-acons var v a)))


(define svex-lookup ((var svar-p) (a svex-alist-p))
  :parents (svex-alist)
  :short "Slow lookup in an @(see svex-alist)."
  :long "<p>See also @(see svex-fastlookup).</p>"
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p))))
  :returns (value? (iff (svex-p value?) value?))
  (mbe :logic (cdr (hons-assoc-equal (svar-fix var) (svex-alist-fix a)))
       :exec (cdr (assoc-equal var a)))
  ///
  (deffixequiv svex-lookup)

  (defthm svex-lookup-of-nil
    (equal (svex-lookup v nil) nil))

  (defthm svex-lookup-of-svex-acons
    (equal (svex-lookup var1 (svex-acons var2 x a))
           (if (equal (svar-fix var1) (svar-fix var2))
               (svex-fix x)
             (svex-lookup var1 a)))
    :hints(("Goal" :in-theory (enable svex-acons)))))


(define svex-fastlookup ((var svar-p) (a svex-alist-p))
  :parents (svex-alist)
  :short "Fast lookup in an @(see svex-alist)."
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p
                                       svex-lookup))))
  :enabled t
  :inline t
  (mbe :logic (svex-lookup var a)
       :exec (cdr (hons-get var a))))


(define svex-alist-keys ((x svex-alist-p))
  :parents (svex-alist)
  :short "Like @(see alist-keys) but with proper @(see fty-discipline) for @(see svex-alist)s."
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :returns (keys svarlist-p)
  (if (atom x)
      nil
    (if (consp (car x))
        (cons (mbe :logic (svar-fix (caar x)) :exec (caar x))
              (svex-alist-keys (cdr x)))
      (svex-alist-keys (cdr x))))
  ///
  (deffixequiv svex-alist-keys
    :hints (("goal" :expand ((svex-alist-fix x)))))

  (defthm member-svex-alist-keys
    (iff (member k (svex-alist-keys x))
         (and (svar-p k)
              (svex-lookup k x)))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defthm svex-alist-keys-of-svex-acons
    (equal (svex-alist-keys (svex-acons k v x))
           (cons (svar-fix k) (svex-alist-keys x)))
    :hints(("Goal" :in-theory (enable svex-acons))))

    (defthm svex-alist-keys-of-pairlis$
    (equal (svex-alist-keys (pairlis$ x y))
           (svarlist-fix x))
    :hints(("Goal" :in-theory (enable svarlist-fix pairlis$ svex-alist-keys)))))


(define svex-alist-vals ((x svex-alist-p))
  :parents (svex-alist)
  :short "Like @(see alist-vals) but with proper @(see fty-discipline) for @(see svex-alist)s."
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :returns (vals svexlist-p)
  (if (atom x)
      nil
    (if (consp (car x))
        (cons (mbe :logic (svex-fix (cdar x)) :exec (cdar x))
              (svex-alist-vals (cdr x)))
      (svex-alist-vals (cdr x))))
  ///
  (deffixequiv svex-alist-vals
    :hints (("goal" :expand ((svex-alist-fix x)))))

  (defthm member-svex-alist-vals-when-svex-lookup
    (implies (svex-lookup k x)
             (member (svex-lookup k x)
                     (svex-alist-vals x)))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defthm svex-alist-vals-of-svex-acons
    (equal (svex-alist-vals (svex-acons k v x))
           (cons (svex-fix v) (svex-alist-vals x)))
    :hints(("Goal" :in-theory (enable svex-acons))))

  (defthm len-of-svex-alist-vals
    (equal (len (svex-alist-vals x))
           (len (svex-alist-keys x)))
    :hints(("Goal" :in-theory (enable svex-alist-keys))))

  (defthm svex-alist-vals-of-pairlis$
    (implies (equal (len x) (len y))
             (equal (svex-alist-vals (pairlis$ x y))
                    (svexlist-fix y)))
    :hints(("Goal" :in-theory (enable svexlist-fix pairlis$ svex-alist-vals)))))




;; Commonly used dumb little functions
(define svex-quoted-index-p ((x svex-p))
  :enabled t
  (and (eq (svex-kind x) :quote)
       (4vec-index-p (svex-quote->val x))))

(define svex-quoted-int-p ((x svex-p))
  :enabled t
  (and (eq (svex-kind x) :quote)
       (2vec-p (svex-quote->val x))))

