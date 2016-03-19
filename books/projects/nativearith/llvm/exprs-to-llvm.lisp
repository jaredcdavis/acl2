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
(include-book "../smallexpr")
(include-book "../smalleval")
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/misc/two-nats-measure" :dir :system)
(local (include-book "misc/assert" :dir :system))
(local (include-book "oslib/catpath" :dir :system))
(local (include-book "std/io/read-file-characters" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/typed-lists/character-listp" :dir :system))
; (depends-on "ops.ll")


(define revappend-intchars ((x integerp) rchars)
  ;; bozo move to string library
  :returns (new-rchars character-listp :hyp (character-listp rchars))
  :inline t
  (b* ((x (ifix x)))
    (if (<= 0 x)
        (revappend-natchars x rchars)
      (revappend-natchars (- x) (cons #\- rchars))))
  ///
  (local (assert!
          (and (equal (rchars-to-string (revappend-intchars 0 nil)) "0")
               (equal (rchars-to-string (revappend-intchars 1 nil)) "1")
               (equal (rchars-to-string (revappend-intchars 15 nil)) "15")
               (equal (rchars-to-string (revappend-intchars -1 nil)) "-1")
               (equal (rchars-to-string (revappend-intchars -37 nil)) "-37")))))


(defsection *ops.ll*
  :parents (llvm-smallops smallexprs-to-llvm)
  :short "LLVM assembly code definitions of the LLVM operations."
  :long "@(def *ops.ll*)"

  (defconsts (*ops.ll* state)
    (acl2::read-file-as-string (oslib::catpath (cbd) "ops.ll") state)))

(defxdoc smallexprs-to-llvm
  :parents (nativearith)
  :short "Compiler from small expressions into LLVM assembly code."

  :long "<p>At a high level, our compiler takes as inputs:</p>

<ul>
<li>The name of the function to produce.</li>
<li>A list of @(see smallexprs) to be compiled.</li>
</ul>

<p>We then produce an @(see llvmasm) structure that contains LLVM assembly code
for a function with a C signature like:</p>

@({
     void myfn (const int64_t* ins, int64_t* outs);
})

<p>That is, the inputs and outputs to the function will simply be arrays of
64-bit integers.  These arrays must be 8-byte aligned and must not overlap.</p>

<p>The input array corresponds to the variables of your expression.  The
particular ordering used can be found in @('llvmasm') structure and is
represented as an @(see llvmvmap), which is a fast alist that binds the
variable names to the indices they have been assigned.</p>

<p>The output array corresponds to the expressions that you have provided.
That is, if you compile a list of 22 expressions, then @('outs') will be a
22-element array and its @('i')th element will correspond to the @('i')th
expression.</p>

<h3>Notes and Todo</h3>

<p>BOZO for nicer interfacing and debugging on the C side, we should probably
generate additional source code files, such as name maps for the input/output
arrays.</p>

<p>The compiler is extremely simple and (unfortunately) really bad.  It doesn't
seem like @('opt') is able to do a very good job of reordering branches to
avoid computing nodes that aren't necessary for the current evaluation.  That
is, we essentially compile:</p>

@({
     (if a (f b) (f c))
      -->
     %cond = ... compilation of a ...
     %true = ... compilation of (f b) ...
     %else = ... compilation of (f c) ...
     %ans  = call i64 @narith_ite(%cond, %true, %else)
})

<p>Where @('narith_ite') is an inline function that does an if-then-else.  It
seems that LLVM (at least in the current way we're invoking it) will basically
translate this into x86 assembly that executes both the true and else branches
and then does a conditional move to choose which one is to become the answer.
That's probably really bad if both branches are expensive.</p>")

(local (xdoc::set-default-parents smallexprs-to-llvm))

(xdoc::order-subtopics smallexprs-to-llvm
                       (smallexprs-to-llvm-top llvmasm))


(defalist llvmvarmap
  :key-type smallvar
  :val-type natp
  :short "Mapping from variables to their indices in the input array."
  :long "<p>The idea here: if we're compiling @('(i64and a (i64or b c))'), then
  we'll give these variables indices, e.g.,</p>

  @({
      a --> 0
      b --> 1
      c --> 2
  })

  <p>These indices will govern where the variable is to be found in the input
  array to the LLVM function.  Typically these assignments are done by @(see
  make-llvmvarmap), but all that really matters is that the assignment
  is unique.</p>")

(defines smallexpr-make-llvmvarmap
  :short "Assign unique, successive indices to the variables of an expression."
  :verify-guards nil
  :flag-local nil

  (define smallexpr-make-llvmvarmap
    ((x      smallexpr-p)
     (n      natp          "Next index to use.")
     (varmap llvmvarmap-p  "Mapping of variables to indices.")
     (seen                 "Seen table to avoid revisiting function calls."))
    :returns
    (mv (new-n natp :rule-classes :type-prescription)
        (new-varmap llvmvarmap-p)
        (new-seen))
    :measure (smallexpr-count x)
    (b* ((x (smallexpr-fix x))
         (n (lnfix n))
         (varmap (llvmvarmap-fix varmap)))
      (smallexpr-case x
        :const (mv n varmap seen)
        :var   (b* ((look (hons-get x.var varmap))
                    ((when look)
                     ;; Already saw this variable, nothing more to do.
                     (mv n varmap seen))
                    ;; This is a new variable, assign it an index.
                    (varmap (hons-acons x.var n varmap))
                    (n (+ 1 n)))
                 (mv n varmap seen))
        :call (b* ((look (hons-get x seen))
                   ((when look)
                    ;; Already visited this node, nothing more to do.
                    (mv n varmap seen))
                   (seen (hons-acons x nil seen)))
                (smallexprlist-make-llvmvarmap (smallexpr-call->args x) n varmap seen)))))

  (define smallexprlist-make-llvmvarmap ((x smallexprlist-p)
                                         (n natp)
                                         (varmap llvmvarmap-p)
                                         (seen))
    :returns (mv (new-n      natp :rule-classes :type-prescription)
                 (new-varmap llvmvarmap-p)
                 (new-seen))
    :measure (smallexprlist-count x)
    (b* ((n (lnfix n))
         (varmap (llvmvarmap-fix varmap))
         ((when (atom x))
          (mv n varmap seen))
         ((mv n varmap seen) (smallexpr-make-llvmvarmap (car x) n varmap seen)))
      (smallexprlist-make-llvmvarmap (cdr x) n varmap seen)))
  ///
  (verify-guards smallexpr-make-llvmvarmap)
  (deffixequiv-mutual smallexpr-make-llvmvarmap)

  ;; BOZO.  Some day prove that this assigns a unique index to every variables.
  ;; The proof is tedious because of preorder traversal.  Something like a
  ;; reusable, general purpose node-collect style argument would be great.
  )


(defalist llvmtemps
  :key-type smallexpr
  :val-type natp
  :short "Mapping from subexpressions to internal node names."

  :long "<p>The general idea here is that to compile an expression like
  @('(i64and a (i64or b c))'), we will create a mapping that binds</p>

  @({
      (i64and a (i64or b c)) --> 1
      a                      --> 2
      (i64or b c)            --> 3
      b                      --> 4
      c                      --> 5
  })

  <p>The mapping is created by @(see smallexpr-make-llvmtemps), which uses a
  simple name index to assign unique indices.  The resulting indices come out
  in an odd order, but all we really care about is that they are unique.</p>

  <p>Note that we assign these temporary indices to all expressions, including
  variables and constants.  This might seem weird, but it is useful when we
  make a heuristic decision about which subexpression to process first.</p>")

(defines smallexpr-make-llvmtemps
  :short "Assign unique names to the nodes of an expression."
  :verify-guards nil
  :flag-local nil

  (define smallexpr-make-llvmtemps ((x     smallexpr-p)
                                    (n     natp         "Smallest name not yet in use.")
                                    (temps llvmtemps-p  "Fast alist."))
    :returns (mv (new-n natp :rule-classes :type-prescription)
                 (new-temps llvmtemps-p))
    :measure (smallexpr-count x)
    (b* ((x     (smallexpr-fix x))
         (n     (lnfix n))
         (temps (llvmtemps-fix temps))

         ;; If we have already assigned a name to this node, we do not need to
         ;; name it again.
         (look (hons-get x temps))
         ((when look)
          (mv n temps))

         ;; Assign the next free index to this node.  Doing this in preorder
         ;; means that the indices of parent nodes can be smaller than the
         ;; indices of their children.  But it gives us a tail call, which is
         ;; nice.
         (temps (hons-acons x n temps))
         (n     (+ 1 n))

         ((unless (smallexpr-case x :call))
          ;; There are no subexpressions to process so we're done.
          (mv n temps)))

      ;; Assign names to the arguments.
      (smallexprlist-make-llvmtemps (smallexpr-call->args x) n temps)))

  (define smallexprlist-make-llvmtemps ((x     smallexprlist-p)
                                        (n     natp)
                                        (temps llvmtemps-p))
    :returns (mv (new-n natp :rule-classes :type-prescription)
                 (new-temps llvmtemps-p))
    :measure (smallexprlist-count x)
    (b* ((n     (lnfix n))
         (temps (llvmtemps-fix temps))
         ((when (atom x))
          (mv n temps))
         ((mv n temps) (smallexpr-make-llvmtemps (car x) n temps)))
      (smallexprlist-make-llvmtemps (cdr x) n temps)))

  ///
  (verify-guards smallexpr-make-llvmtemps)
  (deffixequiv-mutual smallexpr-make-llvmtemps)

  ;; BOZO.  Some day prove this assigns a unique index to every subexpression.
  ;; But the proof is tedious because of, preorder, blah blah blah.
  )


(defalist llvmouts
  :key-type smallexpr
  :val-type nat-list
  :short "Mapping from output expressions to @('out') array index lists."
  :long "<p>We map each expression to a list of indices because, for example,
if we want to compile a list of expressions like @('(a b a)') then we will want
to write the result of @('a') to indices 0 and 2.</p>")

(define make-llvmouts ((exprs smallexprlist-p)
                       (n     natp)
                       (outs  llvmouts-p))
  :returns (mv (new-n natp :rule-classes :type-prescription)
               (outs llvmouts-p))
  (b* ((outs (llvmouts-fix outs))
       (n    (lnfix n))
       ((when (atom exprs))
        (mv n outs))
       (expr1       (car exprs))
       (old-indices (cdr (hons-get expr1 outs)))
       (new-indices (cons n old-indices))
       (outs        (hons-acons expr1 new-indices outs)))
    (make-llvmouts (cdr exprs) (+ 1 n) outs)))


(defun make-smallops-to-llvm (optable)
  (declare (xargs :mode :program))
  (b* (((when (atom optable))
        nil)
       ((list fn args) (car optable)))
    (hons-acons fn
                (cons (cat "@narith_" (str::downcase-string (symbol-name fn)))
                      (len args))
                (make-smallops-to-llvm (cdr optable)))))

(defval *smallops-to-llvm*
  :short "Mapping from smallexpr functions to their LLVM counterparts and arities."
  :showdef nil
  :showval t
  (make-smallops-to-llvm *smalloptable*))

(define smallop-to-llvm ((fn fn-p))
  :returns (mv (llvm-name stringp :rule-classes :type-prescription)
               (arith natp :rule-classes :type-prescription))
  :short "Look up the LLVM counterpart for a function, and its expected arity."
  :long "<p>This is just a lookup in @(see *smallops-to-llvm*).  We make it a
         function only to control the case split that a direct table lookup
         would introduce.</p>"
  (b* ((look (hons-get fn *smallops-to-llvm*))
       ((unless look)
        (raise "Unsupported smallexpr function: ~x0~%" fn)
        (mv "" 0))
       ((cons name arity) (cdr look)))
    (mv name arity)))


(define add-output-stores
  :short "Store instructions to write values to the output array."
  ((tempnum natp            "Index of the %n node being written.")
   (indices nat-listp       "Output indices to write to.")
   (code    character-listp "LLVM assembly code fragment we are building."))
  :returns (code character-listp)
  (b* ((code    (character-list-fix code))
       (tempnum (lnfix tempnum))
       ((when (atom indices))
        code)
       (outnum (lnfix (car indices)))

       ;; Note that before constructing the output map, we explicitly check
       ;; that there are no more than 2^32 outputs, so using i32 here is
       ;; justified and this can't wrap around.

       ;; %o{outnum} = getelementptr i64* %out, i32 {outnum}
       (code (revappend-chars "%o" code))
       (code (revappend-natchars outnum code))
       (code (revappend-chars " = getelementptr i64* %out, i32 " code))
       (code (revappend-natchars outnum code))
       (code (cons #\Newline code))

       ;; We mark all writes to the output array as nontemporal since we aren't
       ;; going to be reading from it.

       ;; store i64 %n{tempnum}, i64* %o{outnum}, align 8, !nontemporal !{i32 1}
       (code (revappend-chars "store i64 %n" code))
       (code (revappend-natchars tempnum code))
       (code (revappend-chars ", i64* %o" code))
       (code (revappend-natchars outnum code))
       (code (revappend-chars ", align 8, !nontemporal !{i32 1}" code))
       (code (cons #\Newline code)))
    (add-output-stores tempnum (cdr indices) code)))

(define add-argument-list
  :short "Argument list for an @('@narith_xxx') call, e.g., @('%n37, %n42, %n74')."
  ((args  smallexprlist-p  "The expressions being given to this function.")
   (temps llvmtemps-p      "Temp map for looking up the @('%n') numbers for each argument.")
   (code  character-listp  "LLVM assembly code fragment we are building."))
  :returns (code character-listp)
  (b* ((code (character-list-fix code))
       ((when (atom args))
        code)
       (arg1 (smallexpr-fix (car args)))
       (tempnum (or (cdr (hons-get arg1 temps))
                    ;; We should be able to eventually get rid of this runtime
                    ;; check by proving that all subexpressions are bound in
                    ;; the temps.
                    (nfix (raise "Missing temp binding: ~x0" arg1))))
       (code (str::revappend-chars "i64 %n" code))
       (code (revappend-natchars tempnum code))
       (code (if (consp (cdr args))
                 (cons #\, code)
               code)))
    (add-argument-list (cdr args) temps code)))

(defines smallexpr-llvm-compile-main

  (define smallexpr-llvm-compile-main
    ((x      smallexpr-p     "Expression to compile.")
     (varmap llvmvarmap-p    "Mapping from input variables to their input array indices.")
     (temps  llvmtemps-p     "Mapping from subexpressions to their temporaries, like n125.")
     (outs   llvmouts-p      "Mapping from output expressions to their output array indices.")
     (seen                   "Seen table so we don't recompile already-compiled expressions.")
     (code   character-listp "Code fragment being produced, as in @(see revappend-chars)."))
    :returns (mv (new-seen)
                 (new-code character-listp))
    :measure (two-nats-measure (smallexpr-count x) 1)
    :verify-guards nil
    (b* ((x      (smallexpr-fix x))
         (varmap (llvmvarmap-fix varmap))
         (temps  (llvmtemps-fix temps))
         (outs   (llvmouts-fix outs))
         (code   (character-list-fix code))

         (look (hons-get x seen))
         ((when look)
          ;; Already processed this node, nothing more to do.
          (mv seen code))

         (seen
          ;; Mark this node as seen since we're going to process it now.
          (hons-acons x nil seen))
         (tempnum (or (cdr (hons-get x temps))
                      ;; We should be able to eventually get rid of this runtime
                      ;; check by proving that all subexpressions are bound in
                      ;; the temps.
                      (nfix (raise "Missing temp binding: ~x0" x))))

         ((mv seen code)
          ;; We now carry out the main computation for this node.  By the end
          ;; of this binding, we will have processed the node except perhaps
          ;; for writing to the output array.
          (smallexpr-case x

            :const
            ;; LLVM doesn't seem to have an instruction like %foo = 3.
            ;; However, per some experiments it seems smart enough to resolve
            ;; a+0 to just a, so we'll implement constants just as adds.  This
            ;; is handy because it means that constants are just like any other
            ;; nodes in that their results get stored in a temporary like
            ;; %n127, instead of having to be treated specially when we write
            ;; out argument lists and so forth.
            (b* (;; %n{tempnum} = add i64 0, {value}
                 (code (revappend-chars "%n" code))
                 (code (revappend-natchars tempnum code))
                 (code (revappend-chars " = add i64 0, " code))
                 (code (revappend-intchars x.val code))
                 (code (cons #\Newline code)))
              (mv seen code))

            :var
            ;; We need to:
            ;;  (1) Figure out its address in the input array, and then
            ;;  (2) Load that into its %n node.
            (b* ((varnum (or (cdr (hons-get x.var varmap))
                             ;; We should be able to eventually get rid of this
                             ;; runtime check by proving all variables are bound
                             ;; in the varmap.
                             (nfix (raise "Missing var binding: ~x0" x.var))))

                 ;; %i{varnum} = getelementptr i64* %in, i32 {varnum}
                 (code (revappend-chars "%i" code))
                 (code (revappend-natchars varnum code))
                 ;; Note that after constructing the variable map, we explicitly
                 ;; check that there are no more than 2^32 variables, so using i32
                 ;; here is justified and this can't wrap around.
                 (code (revappend-chars " = getelementptr i64* %in, i32 " code))
                 (code (revappend-natchars varnum code))
                 (code (cons #\Newline code))

                 ;; %n{tempnum} = load i64* %i{___}, align 8
                 (code (revappend-chars "%n" code))
                 (code (revappend-natchars tempnum code))
                 (code (revappend-chars " = load i64* %i" code))
                 (code (revappend-natchars varnum code))
                 (code (revappend-chars ", align 8" code))
                 (code (cons #\Newline code)))
              (mv seen code))

            :call
            (b* (;; Nothing in the smallexpr syntax constrains the allowed
                 ;; functions or their arities.  But of course we only have
                 ;; LLVM primitives for the functions that we have implemented
                 ;; so far, and they have fixed arities.  At any rate, let's
                 ;; explicitly check for operators that we understand and blow
                 ;; up if anything is wrong.
                 ((mv llvm-fn arity) (smallop-to-llvm x.fn))
                 ((unless (equal (len x.args) arity))
                  (raise "Bad arity for function ~x0: expected ~x1 args but got ~x2: ~x3"
                         x.fn arity (len x.args) x)
                  (mv seen code))

                 ;; BOZO this is really stupid.  We basically just compile all
                 ;; the arguments and then call the corresponding LLVM
                 ;; function.  This is a really stupid way to do it for
                 ;; If/Then/Else operators and might often be stupid for things
                 ;; like And/Or, where we could often short-circuit the
                 ;; evaluation.  We could probably get a lot of mileage out of
                 ;; a smarter compiler.
                 ((mv seen code)
                  ;; Compile the arguments to their %n{___} numbers are computed
                  (smallexprlist-llvm-compile-main x.args varmap temps outs seen code))
                 ;; %n{tempnum} = call i64 @narith_{fn} (%n{___}, %n{___})
                 (code (revappend-chars "%n" code))
                 (code (revappend-natchars tempnum code))
                 (code (revappend-chars " = call i64 " code))
                 (code (revappend-chars llvm-fn code))
                 (code (cons #\( code))
                 (code (add-argument-list x.args temps code))
                 (code (cons #\) code))
                 (code (cons #\Newline code)))
              (mv seen code))))

         ;; By now we have added the code to generate %n{tempnum}, so we are
         ;; basically done compiling X.  The only thing left to do is: if X
         ;; happens to be an output node, then we should go ahead and write its
         ;; value to its output.  It seems better to do this here, instead of
         ;; waiting and writing all of the outputs at the end, because at this
         ;; point %n{tempnum} has just been computed so its value is certainly
         ;; just sitting there in a register, waiting to be used.
         (outnums (cdr (hons-get x outs)))
         ((unless (consp outnums))
          ;; Not an output, so no write needs to occur.  We're all finished.
          (mv seen code))
         (code (add-output-stores tempnum outnums code)))
      (mv seen code)))

  (define smallexprlist-llvm-compile-main ((x      smallexprlist-p)
                                           (varmap llvmvarmap-p)
                                           (temps  llvmtemps-p)
                                           (outs   llvmouts-p)
                                           (seen)
                                           (code   character-listp))
    :returns (mv (new-seen)
                 (new-code character-listp))
    :measure (two-nats-measure (smallexprlist-count x) 0)
    (b* ((code (character-list-fix code))
         ((when (atom x))
          (mv seen code))
         ((mv seen code)
          (smallexpr-llvm-compile-main (car x) varmap temps outs seen code)))
      (smallexprlist-llvm-compile-main (cdr x) varmap temps outs seen code)))

  ///
  (verify-guards smallexpr-llvm-compile-main)
  (deffixequiv-mutual smallexpr-llvm-compile-main))



(defprod llvmasm
  :short "LLVM assembly code for some @(see smallexpr)s."
  :tag :llvmasm
  ((fnname stringp :rule-classes :type-prescription
           "Name of the LLVM function that was generated.")
   (code stringp :rule-classes :type-prescription
         "LLVM assembly code for this function, and supporting operations.")
   (outs   smallexprlist-p
           "Expressions that this code fragment represents.")
   (varmap llvmvarmap-p
           "Fast alist mapping of variables to input array indices.")))


(defval *smallexprs-to-llvm-prelude*
  :short "Same as @(see *ops.ll*), but changes all functions to be private."
  (str::revappend-chars (str::strsubst "define" "define private" *ops.ll*)
                        nil))

(define smallexprs-to-llvm-top
  :short "Top level compiler from small expressions to LLVM."
  ((fnname stringp         "Name of the LLVM function to produce.")
   (x      smallexprlist-p "Expressions to compile."))
  :returns (compiled llvmasm-p)

  (b* (;; Construct input mapping (variables to input array indices)
       ((mv num-inputs varmap seen)
        (smallexprlist-make-llvmvarmap x 0 nil nil))
       (- (fast-alist-free seen))
       (- (or (< num-inputs (expt 2 32))
              (raise "Only 2^32 inputs are supported, but these expressions have ~x0 variables."
                     num-inputs)))

       ;; Construct output mapping (elements of X to output array indices)
       ((mv num-outputs outs) (make-llvmouts x 0 nil))
       (- (or (< num-outputs (expt 2 32))
              (raise "Only 2^32 outputs are supported, but given ~x0 expressions."
                     num-outputs)))

       ;; Construct temp mapping (every expression to its %n number)
       ((mv num-temps temps)
        (smallexprlist-make-llvmtemps x 0 nil))

       (code *smallexprs-to-llvm-prelude*)
       (code (cons #\Newline code))
       (code (str::revappend-chars "define void @" code))
       (code (str::revappend-chars fnname code))
       (code (str::revappend-chars " (i64* noalias nocapture align 8 %in,
                                      i64* noalias nocapture align 8 %out) {" code))
       (code (cons #\Newline code))
       ((mv seen code)
        (smallexprlist-llvm-compile-main x varmap temps outs
                                         num-temps ;; seen table -- just a size hint
                                         code))
       (code (str::revappend-chars "ret void" code))
       (code (cons #\Newline code))
       (code (str::revappend-chars "}" code))
       (code (cons #\Newline code)))

    ;; BOZO do we want to also free the varmap?  Maybe not, since we return it.
    (fast-alist-free seen)
    (fast-alist-free temps)
    (fast-alist-free outs)
    (make-llvmasm :fnname fnname
                  :code (str::rchars-to-string code)
                  :outs x
                  :varmap varmap)))


