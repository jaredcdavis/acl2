;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

;; ===================================================================

(in-package "X86ISA")
(include-book "x86" :ttags :all :dir :machine)
(include-book "tools/mv-nth" :dir :system)
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

;; ======================================================================

(defsection proof-utilities
  :parents (x86isa)
  :short "Basic utilities for x86 machine-code proofs"
  )

;; ======================================================================

;; lemma-1 and lemma-2 are expensive, no doubt, but they help in
;; getting the ModR/M, SIB, prefix present, etc. bytes when the
;; hypotheses of x86-fetch-decode-opener are being relieved by
;; inducing ACL2 to do backchaining.  I should think about formulating
;; these two lemmas more efficiently.

(defthmd lemma-1
  (implies (< x y)
           (not (equal x y))))

(defthmd lemma-2
  (implies (< y x)
           (not (equal x y))))

;; ======================================================================
;; Some useful arithmetic theorems, currently placed here because
;; they've yet to find a good home:

(defthm loghead-smaller
  (implies (and (equal (loghead n x) 0)
                (natp n)
                (<= m n))
           (equal (loghead m x) 0))
  :hints (("Goal" :in-theory (e/d*
                              (acl2::ihsext-recursive-redefs
                               acl2::ihsext-inductions)
                              ()))))

(defthm loghead-unequal
  (implies (and (signed-byte-p x a)
                (signed-byte-p x b)
                (not (equal a b))
                (natp x))
           (equal (equal (loghead x a) (loghead x b)) nil))
  :hints
  (("Goal" :in-theory
    (e/d* (acl2::ihsext-inductions acl2::ihsext-recursive-redefs)
          (signed-byte-p)))))

(defthm putting-logior-loghead-ash-logtail-together
  (implies (and (syntaxp (quotep n))
                (unsigned-byte-p (* 2 n) x)
                (natp n))
           (equal (logior (loghead n x)
                          (ash (logtail n x) n))
                  x))
  :hints (("Goal" :in-theory
           (e/d (loghead logtail logior-expt-to-plus-quotep)
                ()))))

;; (defthm putting-logior-loghead-ash-logtail-together
;;   (implies (and (syntaxp (quotep n))
;;                 (<= m n)
;;                 (unsigned-byte-p m x)
;;                 (natp n))
;;            (equal (logior (loghead n x)
;;                           (ash (logtail n x) n))
;;                   (loghead n x)))
;;   :hints (("Goal" :in-theory (e/d (loghead logtail logior-expt-to-plus-quotep)
;;                                   nil))))

;; ======================================================================

;; Adding untranslate patterns for readability while doing code
;; proofs: for example, (rgfi 0 x86) will show up as (rgfi *rax* x86).

(include-book "misc/untranslate-patterns" :dir :system)

;; General-Purpose Registers:

(defun stobj-1D-arr-idx-untranslate (function-symb args-match indices names)
  (declare (xargs :guard (and (equal (len indices) (len names))
                              (true-listp args-match)
                              (nat-listp indices)
                              (true-listp names)
                              (symbolp function-symb))))

  (if (mbt (and (symbolp function-symb)
                (equal (len indices) (len names))))

      (if (endp indices)
          nil
        (cons
         `(acl2::add-untranslate-pattern-function
           (,function-symb (quote ,(car indices)) ,@args-match)
           (,function-symb ,(car names) ,@args-match))
         (stobj-1D-arr-idx-untranslate
          function-symb args-match (cdr indices) (cdr names))))

    nil))


;; General-Purpose Registers:

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   'rgfi
   '(?x)
   (gl-int 0 1 24)
   '(*RAX* *RCX* *RDX* *RBX* *RSP* *RBP* *RSI* *RDI*
           *R0*  *R1*  *R2*  *R3*  *R4*  *R5*  *R6*  *R7*
           *R8*  *R9*  *R10* *R11* *R12* *R13* *R14* *R15*))))

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   '!rgfi
   '(?v ?x)
   (gl-int 0 1 24)
   '(*RAX* *RCX* *RDX* *RBX* *RSP* *RBP* *RSI* *RDI*
           *R0*  *R1*  *R2*  *R3*  *R4*  *R5*  *R6*  *R7*
           *R8*  *R9*  *R10* *R11* *R12* *R13* *R14* *R15*))))

;; Segment Registers:

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   'segi
   '(?x)
   (gl-int 0 1 6)
   '(*ES* *CS* *SS* *DS* *FS* *GS*))))

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   '!segi
   '(?v ?x)
   (gl-int 0 1 6)
   '(*ES* *CS* *SS* *DS* *FS* *GS*))))

;; Control Registers:

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   'ctri
   '(?x)
   (gl-int 0 1 18)
   '(*MSW* *CR0* *CR1* *CR2* *CR3* *CR4* *CR5* *CR6* *CR7*
           *CR8* *CR9*  *CR10* *CR11* *CR12* *CR13* *CR14* *CR15*
           *XCR0*))))

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   '!ctri
   '(?v ?x)
   (gl-int 0 1 18)
   '(*MSW* *CR0* *CR1* *CR2* *CR3* *CR4* *CR5* *CR6* *CR7*
           *CR8* *CR9*  *CR10* *CR11* *CR12* *CR13* *CR14* *CR15*
           *XCR0*))))


;; Model-Specific Registers:

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   'msri
   '(?x)
   ;; Note that in case of MSRs, the indices 0 through 7 are actually
   ;; the values of the constants *IA32_EFER-IDX*, *IA32_FS_BASE-IDX*,
   ;; and so on.  The constants below have the correct register
   ;; addresses, as specified by the Intel manuals. See
   ;; utilities/constants.lisp for details.
   (gl-int 0 1 7)
   '(*IA32_EFER* *IA32_FS_BASE* *IA32_GS_BASE* *IA32_KERNEL_GS_BASE*
                 *IA32_STAR* *IA32_LSTAR* *IA32_FMASK*))))

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   '!msri
   '(?v ?x)
   (gl-int 0 1 7)
   '(*IA32_EFER* *IA32_FS_BASE* *IA32_GS_BASE* *IA32_KERNEL_GS_BASE*
                 *IA32_STAR* *IA32_LSTAR* *IA32_FMASK*))))

;; Flags:

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   'flgi
   '(?x)
   '(0 2 4 6 7 8 9 10 11 12 14 16 17 18 19 20 21)
   '(*cf* *pf* *af* *zf* *sf* *tf* *if* *df* *of*
          *iopl *nt* *rf* *vm* *ac* *vif* *vip* *id*))))


(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   '!flgi
   '(?v ?x)
   '(0 2 4 6 7 8 9 10 11 12 14 16 17 18 19 20 21)
   '(*cf* *pf* *af* *zf* *sf* *tf* *if* *df* *of*
          *iopl *nt* *rf* *vm* *ac* *vif* *vip* *id*))))

(make-event
 (cons
  'progn
  (stobj-1D-arr-idx-untranslate
   '!flgi-undefined$inline
   '(?x)
   '(0 2 4 6 7 11)
   '(*cf* *pf* *af* *zf* *sf* *of*))))

(acl2::optimize-untranslate-patterns)

;; ======================================================================
