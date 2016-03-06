;; AUTHOR:
;; Cuong Chau <ckcuong@cs.utexas.edu>

;; All events beginning with the prefix RTL:: in this book are
;; imported from the RTL/REL11 library under the directory
;; "books/rtl/rel11/lib", authored by David M. Russinoff
;; (david@russinoff.com).

(in-package "X86ISA")
(include-book "constants" :dir :utils)
(include-book "rtl/rel11/portcullis" :dir :system)
(include-book "tools/with-supporters" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (e/d (bitops::ash-1-removal) ())))

;; ======================================================================

(defsection floating-point-sqrt-specifications
  :parents (floating-point-arithmetic-specifications)
  :short "Specification of SQRT operation"
  )

(local (xdoc::set-default-parents floating-point-sqrt-specifications))

;; ======================================================================

;; SQRT:

(ACL2::with-supporters
 (local (include-book "rtl/rel11/lib/excps" :dir :system))
 :names (rtl::formal-+ rtl::cat rtl::cat-size)

 (in-theory (e/d () (rtl::sse-sqrt-spec)))

 (defun sse-sqrt (operand mxcsr exp-width frac-width)
   (declare (xargs :guard (and (natp operand)
                               (n32p mxcsr)
                               (posp exp-width)
                               (posp frac-width))))
   (b* (((mv result mxcsr)
         (ec-call
          (rtl::sse-sqrt-spec
           operand mxcsr (list nil (1+ frac-width) exp-width))))
        ;; Hopefully, the following fixes will go away once we know
        ;; rtl::sse-binary-spec returns a well-formed result and
        ;; mxcsr.
        (result (loghead (+ 1 exp-width frac-width) (ifix result)))
        (mxcsr (loghead 32 (ifix mxcsr)))
        ;; Pre-computation Exceptions
        ;; Check invalid operation
        ((when (and (equal (mxcsr-slice :ie mxcsr) 1)
                    (equal (mxcsr-slice :im mxcsr) 0)))
         (mv 'invalid-operand-exception-is-not-masked result mxcsr))
        ;; Check denormal operand
        ((when (and (equal (mxcsr-slice :de mxcsr) 1)
                    (equal (mxcsr-slice :dm mxcsr) 0)))
         (mv 'denormal-operand-exception-is-not-masked result mxcsr))
        ;; Post-computation Exceptions
        ;; Check precision
        ((when (and (equal (mxcsr-slice :pe mxcsr) 1)
                    (equal (mxcsr-slice :pm mxcsr) 0)))
         (mv 'precision-exception-is-not-masked result mxcsr)))
     (mv nil result mxcsr))))

(defthm unsigned-byte-p-of-result-of-sse-sqrt
  (implies (and (equal fp-width (+ 1 exp-width frac-width))
                (posp exp-width)
                (posp frac-width))
           (unsigned-byte-p fp-width
                            (mv-nth 1 (sse-sqrt op mxcsr exp-width frac-width)))))

(defthm unsigned-byte-p-of-mxcsr-of-sse-sqrt
  (unsigned-byte-p 32 (mv-nth 2 (sse-sqrt op mxcsr exp-width frac-width))))

(in-theory (disable sse-sqrt))

;; ======================================================================

;; Single-Precision Operation:

(define sp-sse-sqrt ((x     :type (unsigned-byte 32))
                     (mxcsr :type (unsigned-byte 32)))
  (sse-sqrt x mxcsr #.*IEEE-SP-EXP-WIDTH* #.*IEEE-SP-FRAC-WIDTH*)

  ///

  (defthm-usb n32p-result-sp-sse-sqrt
    :bound 32
    :concl (mv-nth 1 (sp-sse-sqrt x mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mxcsr-sp-sse-sqrt
    :bound 32
    :concl (mv-nth 2 (sp-sse-sqrt x mxcsr))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

;; Double-Precision Operation:

(define dp-sse-sqrt ((x     :type (unsigned-byte 64))
                     (mxcsr :type (unsigned-byte 32)))
  (sse-sqrt x mxcsr #.*IEEE-DP-EXP-WIDTH* #.*IEEE-DP-FRAC-WIDTH*)

  ///
  (defthm-usb n64p-result-dp-sse-sqrt
    :bound 64
    :concl (mv-nth 1 (dp-sse-sqrt x mxcsr))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mxcsr-dp-sse-sqrt
    :bound 32
    :concl (mv-nth 2 (dp-sse-sqrt x mxcsr))
    :hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
    :gen-type t
    :gen-linear t))

;; ======================================================================
