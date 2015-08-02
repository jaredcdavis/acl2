;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

;; This book contains the specification of the following instructions:
;; sal  sar  shl  shr  rcl  rcr  rol  ror

(in-package "X86ISA")

(include-book "../x86-decoding-and-spec-utils"
	      :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

(include-book "centaur/bitops/fast-rotate" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (in-theory (e/d ()
		       (bitops::logand-with-negated-bitmask
			force (force)))))

;; Note: SRC operand is either an (unsigned-byte 6) or (unsigned-byte
;; 5) since it is masked before the actual rotate or shift
;; operations.

;; ======================================================================

(encapsulate
 ()

 (local (include-book "arithmetic-5/top" :dir :system))

 (defthm weed-out-irrelevant-logand-when-first-operand-constant
   (implies (and
	     ;; syntaxp will restrict the application of this
	     ;; theorem...
	     (syntaxp (quotep x))
	     (unsigned-byte-p n y)
	     (equal (logand (1- (expt 2 n)) x) (1- (expt 2 n))))
	    (equal (logand x y) y))
   :hints (("Goal"
	    :use ((:instance acl2::mod-logand (x x) (y y) (n n)))
	    :in-theory (disable acl2::mod-logand))))
 )

;; ======================================================================

;; Rotates:

(define rcl-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (let* ((size-1 (1- size))
	 (size+1 (1+ size))
	 (neg-size (- size))
	 (neg-size-1 (- size-1))
	 (fn-name (mk-name "RCL-SPEC-" size))
	 (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst :type (unsigned-byte ,size))
	(src :type (unsigned-byte 6)
	     "We assume @('src') has been masked appropriately by the decoding part of the rotate instructions.")
	(input-rflags :type (unsigned-byte 32)))

       :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
       :parents (rcl-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
		      :exec dst))
	    (src (mbe :logic (n-size 6 src)
		      :exec src))
	    (input-rflags (mbe :logic (n32 input-rflags)
			       :exec input-rflags))
	    (old-cf (the (unsigned-byte 1)
		      (rflags-slice :cf input-rflags)))

	    (new-dst     (mbe :logic (part-install old-cf dst
						   :low ,size :width 1)
			      :exec (the (unsigned-byte
					  ,size+1)
				      (logior (the (unsigned-byte ,size+1)
						(ash old-cf ,size))
					      dst))))
	    (raw-result  (the (unsigned-byte ,size+1)
						   (fast-rotate-left new-dst ,size+1 src)))
	    (result      (the (unsigned-byte ,size) (n-size ,size raw-result)))

	    ((mv (the (unsigned-byte 32) output-rflags)
		 (the (unsigned-byte 32) undefined-flags))

	     (case src
	       (0
		;; No flags affected
		(mv input-rflags 0))
	       (1
		;; CF and OF are the only affected flags.
		(b* ((cf
		      ;; CF = MSB of the raw-result.
		      (mbe :logic (logbit ,size raw-result)
			   :exec (logand 1
					 (the (unsigned-byte 1)
					   (ash (the (unsigned-byte ,size+1)
						  raw-result)
						,neg-size)))))
		     (of
		      ;; OF = XOR of the CF bit after the rotate and the
		      ;; MSB of the result
		      (b-xor cf (mbe :logic (logbit ,size-1 result)
				     :exec (logand 1
						   (the (unsigned-byte 1)
						     (ash (the (unsigned-byte ,size)
							    result)
							  ,neg-size-1))))))

		     (output-rflags (the (unsigned-byte 32)
				      (!rflags-slice
				       :cf cf
				       (!rflags-slice
					:of of input-rflags)))))
		    (mv output-rflags 0)))
	       (otherwise
		;; CF is affected, OF is undefined.
		;; All other flags are unaffected.
		(b* ((cf ;; CF = MSB of the raw-result.
		      (mbe :logic (logbit ,size raw-result)
			   :exec (logand 1
					 (the (unsigned-byte 1)
					   (ash (the (unsigned-byte ,size+1)
						  raw-result)
						,neg-size)))))
		     (output-rflags
		      (the (unsigned-byte 32)
			(!rflags-slice :cf cf input-rflags)))

		     (undefined-flags (the (unsigned-byte 32)
					(!rflags-slice :of 1 0))))
		    (mv output-rflags undefined-flags)))))

	    (output-rflags (mbe :logic (n32 output-rflags)
				:exec output-rflags)))

	   (mv result output-rflags undefined-flags))

       ///

       (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	 :bound ,size
	 :concl (mv-nth 0 (,fn-name dst src input-rflags))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	 :bound 32
	 :concl (mv-nth 1 (,fn-name dst src input-rflags))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	 :bound 32
	 :concl (mv-nth 2 (,fn-name dst src input-rflags))
	 :gen-type t
	 :gen-linear t))
    ))

(make-event (rcl-spec-gen  8))
(make-event (rcl-spec-gen 16))
(make-event (rcl-spec-gen 32))
(make-event (rcl-spec-gen 64))

(define rcl-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (n06p src)
	      (case size
		(1 (n08p dst))
		(2 (n16p dst))
		(4 (n32p dst))
		(8 (n64p dst))
		(otherwise nil)))

  :inline t

  :parents (x86-instruction-semantics)
  :short "Specification for the @('RCL') instruction"
  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set
  Reference \(N-Z\).</p>

<p>The RCL instruction shifts the CF flag into the least-significant
bit and shifts the most-significant bit into the CF flag. ... The OF
flag is defined only for the 1-bit rotates; it is undefined in all
other cases \(except RCL and RCR instructions only: a zero-bit rotate
does nothing, that is affects no flags\). For left rotates, the OF
flag is set to the exclusive OR of the CF bit \(after the rotate\) and
the most-significant bit of the result.</p>"

  (case size
    (1 (rcl-spec-8  dst src input-rflags))
    (2 (rcl-spec-16 dst src input-rflags))
    (4 (rcl-spec-32 dst src input-rflags))
    (8 (rcl-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-rcl-spec
    (natp (mv-nth 0 (rcl-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-usb n32p-mv-nth-1-rcl-spec
    :bound 32
    :concl (mv-nth 1 (rcl-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mv-nth-2-rcl-spec
    :bound 32
    :concl (mv-nth 2 (rcl-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)
  )

(define rol-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (let* ((size-1 (1- size))
	 (size+1 (1+ size))
	 (neg-size-1 (- (1- size)))
	 (fn-name (mk-name "ROL-SPEC-" size))
	 (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst    :type (unsigned-byte ,size))
	(src    :type (unsigned-byte 6)
		"We assume @('src') has been masked appropriately by the decoding part of the rotate instructions.")
	(input-rflags :type (unsigned-byte 32)))

       :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
       :parents (rol-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
		      :exec dst))
	    (src (mbe :logic (n-size 6 src)
		      :exec src))
	    (input-rflags (mbe :logic (n32 input-rflags)
			       :exec input-rflags))

	    (result  (mbe :logic
			  (n-size ,size (the (unsigned-byte ,size+1) (fast-rotate-left dst ,size src)))
			  :exec
			  (the (unsigned-byte ,size) (fast-rotate-left dst ,size src))))

	    ((mv (the (unsigned-byte 32) output-rflags)
		 (the (unsigned-byte 32) undefined-flags))

	     (case src
	       (0
		;; No flags, except OF, affected. OF is undefined.
		(b* ((undefined-flags (the (unsigned-byte 32)
					(!rflags-slice :of 1 0))))
		  (mv input-rflags undefined-flags)))
	       (1
		;; CF and OF are the only affected flags.
		(b* ((cf
		      ;; CF = LSB of the  result.
		      (mbe :logic ;; (logbit 0 result)
			   (part-select result :low 0 :width 1)
			   :exec (the (unsigned-byte 1)
				   (logand 1 (the (unsigned-byte ,size)
					       result)))))
		     (of
		      ;; OF = XOR of the CF bit after the rotate and the
		      ;; MSB of the result
		      (b-xor cf (mbe :logic (logbit ,size-1 result)
				     :exec (logand 1
						   (the (unsigned-byte 1)
						     (ash (the (unsigned-byte ,size)
							    result)
							  ,neg-size-1))))))

		     (output-rflags (the (unsigned-byte 32)
				      (!rflags-slice
				       :cf cf
				       (!rflags-slice
					:of of input-rflags)))))
		  (mv output-rflags 0)))

	       (otherwise
		;; CF is affected, OF is undefined.
		;; All other flags are unaffected.

		(b* ((cf          ;; CF = LSB of the result.
		      (mbe :logic ;; (logbit 0 result)
			   (part-select result :low 0 :width 1)
			   :exec
			   (the (unsigned-byte 1)
			     (logand 1 (the (unsigned-byte ,size)
					 result)))))
		     (output-rflags (the (unsigned-byte 32)
				      (!rflags-slice
				       :cf cf
				       input-rflags)))
		     (undefined-flags
		      (the (unsigned-byte 32)
			(!rflags-slice :of 1 0))))
		  (mv output-rflags undefined-flags)))))

	    (output-rflags (mbe :logic (n32 output-rflags)
				:exec output-rflags)))

	 (mv result output-rflags undefined-flags))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	 :bound ,size
	 :concl (mv-nth 0 (,fn-name dst src input-rflags))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	 :bound 32
	 :concl (mv-nth 1 (,fn-name dst src input-rflags))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	 :bound 32
	 :concl (mv-nth 2 (,fn-name dst src input-rflags))
	 :gen-type t
	 :gen-linear t))
    ))

(make-event (rol-spec-gen  8))
(make-event (rol-spec-gen 16))
(make-event (rol-spec-gen 32))
(make-event (rol-spec-gen 64))

(define rol-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and
	  (n06p src)
	  (case size
	    (1  (n08p dst))
	    (2  (n16p dst))
	    (4  (n32p dst))
	    (8  (n64p dst))
	    (otherwise nil)))

  :inline t
  :parents (x86-instruction-semantics)
  :short "Specification for the @('ROL') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set
  Reference \(N-Z\).</p>

<p>For the ROL and ROR instructions, the original value of the CF flag
is not a part of the result, but the CF flag receives a copy of the
bit that was shifted from one end to the other. ... The OF flag is
defined only for the 1-bit rotates; it is undefined in all other cases
\(except ROL and RCR instructions only: a zero-bit rotate does
nothing, that is affects no flags\). For left rotates, the OF flag is
set to the exclusive OR of the CF bit \(after the rotate\) and the
most-significant bit of the result.</p>"

  (case size
    (1 (rol-spec-8  dst src input-rflags))
    (2 (rol-spec-16 dst src input-rflags))
    (4 (rol-spec-32 dst src input-rflags))
    (8 (rol-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-rol-spec
    (natp (mv-nth 0 (rol-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-usb n32p-mv-nth-1-rol-spec
    :bound 32
    :concl (mv-nth 1 (rol-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mv-nth-2-rol-spec
    :bound 32
    :concl (mv-nth 2 (rol-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

(define rcr-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (let* ((size-1 (1- size))
	 (size-2 (- size 2))
	 (size+1 (1+ size))
	 (neg-size (- size))
	 (neg-size-1 (- size-1))
	 (neg-size-2 (- size-2))
	 (fn-name (mk-name "RCR-SPEC-" size))
	 (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst    :type (unsigned-byte ,size))
	(src    :type (unsigned-byte 6)
		"We assume @('src') has been masked appropriately by the decoding part of the rotate instructions.")
	(input-rflags :type (unsigned-byte 32)))

       :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
       :parents (rcr-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
		      :exec dst))
	    (src (mbe :logic (n-size 6 src)
		      :exec src))
	    (input-rflags (mbe :logic (n32 input-rflags)
			       :exec input-rflags))

	    (input-cf (the (unsigned-byte 1)
			(rflags-slice :cf input-rflags)))

	    (new-dst     (mbe :logic (part-install input-cf dst
						   :low ,size :width 1)
			      :exec (the (unsigned-byte
					  ,size+1)
				      (logior (the (unsigned-byte ,size+1)
						(ash input-cf ,size))
					      dst))))
	    (raw-result  (the (unsigned-byte ,size+1) (fast-rotate-right new-dst ,size+1 src)))
	    (result      (the (unsigned-byte ,size) (n-size ,size raw-result)))

	    ((mv (the (unsigned-byte 32) output-rflags)
		 (the (unsigned-byte 32) undefined-flags))

	     (case src
	       (0
		;; No flags affected
		(mv input-rflags 0))

	       (1
		;; CF and OF are the only affected flags.
		(b* ((cf
		      ;; CF = MSB of the raw-result.
		      (mbe :logic (logbit ,size raw-result)
			   :exec (logand 1
					 (the (unsigned-byte 1)
					   (ash (the (unsigned-byte ,size+1)
						  raw-result)
						,neg-size)))))
		     (of
		      ;; OF = XOR of the two most significant bits of
		      ;; the result.
		      (b-xor (mbe :logic (logbit ,size-1 result)
				  :exec (logand 1
						(the (unsigned-byte 1)
						  (ash (the (unsigned-byte ,size)
							 result)
						       ,neg-size-1))))
			     (mbe :logic ;; (logbit ,size-2 result)
				  (part-select result :low ,size-2 :width 1)
				  :exec (logand 1
						(the (unsigned-byte 2)
						  (ash (the (unsigned-byte ,size)
							 result)
						       ,neg-size-2))))))

		     (output-rflags (the (unsigned-byte 32)
				      (!rflags-slice
				       :cf cf
				       (!rflags-slice
					:of of input-rflags)))))
		  (mv output-rflags 0)))

	       (otherwise
		;; CF is affected, OF is undefined.
		;; All other flags are unaffected.
		(b* ((cf ;; CF = MSB of the raw-result.
		      (mbe :logic (logbit ,size raw-result)
			   :exec (the (unsigned-byte 1)
				   (logand 1
					   (the (unsigned-byte 1)
					     (ash (the (unsigned-byte ,size+1)
						    raw-result)
						  ,neg-size))))))

		     (output-rflags (the (unsigned-byte 32)
				      (!rflags-slice
				       :cf cf
				       input-rflags)))

		     (undefined-flags (the (unsigned-byte 32)
					(!rflags-slice :of 1 0))))
		  (mv output-rflags undefined-flags))))))

	 (mv result output-rflags undefined-flags))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	 :bound ,size
	 :concl (mv-nth 0 (,fn-name dst src output-rflags))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	 :bound 32
	 :concl (mv-nth 1 (,fn-name dst src output-rflags))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	 :bound 32
	 :concl (mv-nth 2 (,fn-name dst src output-rflags))
	 :gen-type t
	 :gen-linear t))
    ))

(make-event (rcr-spec-gen  8))
(make-event (rcr-spec-gen 16))
(make-event (rcr-spec-gen 32))
(make-event (rcr-spec-gen 64))

(define rcr-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (n06p src)
	      (case size
		(1 (n08p dst))
		(2 (n16p dst))
		(4 (n32p dst))
		(8 (n64p dst))
		(otherwise nil)))


  :inline t

  :parents (x86-instruction-semantics)
  :short "Specification for the @('RCR') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set
  Reference \(N-Z\).</p>

<p>The RCR instruction shifts the CF flag into the most-significant
bit and shifts the least-significant bit into the CF flag. ... The OF
flag is defined only for the 1-bit rotates; it is undefined in all
other cases \(except RCL and RCR instructions only: a zero-bit rotate
does nothing, that is affects no flags\).  For right rotates, the OF
flag is set to the exclusive OR of the two most-significant bits of
the result.</p>"

  (case size
    (1 (rcr-spec-8  dst src input-rflags))
    (2 (rcr-spec-16 dst src input-rflags))
    (4 (rcr-spec-32 dst src input-rflags))
    (8 (rcr-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-rcr-spec
    (natp (mv-nth 0 (rcr-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-usb n32p-mv-nth-1-rcr-spec
    :bound 32
    :concl (mv-nth 1 (rcr-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mv-nth-2-rcr-spec
    :bound 32
    :concl (mv-nth 2 (rcr-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

(define ror-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (b* ((size-1 (1- size))
       (size-2 (- size 2))
       (?size+1 (1+ size))
       (neg-size-1 (- size-1))
       (neg-size-2 (- size-2))
       (fn-name (mk-name "ROR-SPEC-" size))
       (str-nbits (if (eql size 8) "08" size)))

    `(define ,fn-name
       ((dst    :type (unsigned-byte ,size))
	(src    :type (unsigned-byte 6)
		"We assume @('src') has been masked appropriately by the decoding part of the rotate instructions.")
	(input-rflags :type (unsigned-byte 32)))

       :guard-hints (("Goal" :in-theory (e/d () (unsigned-byte-p))))
       :parents (ror-spec)

       (b* ((dst (mbe :logic (n-size ,size dst)
		      :exec dst))
	    (src (mbe :logic (n-size 6 src)
		      :exec src))
	    (input-rflags (mbe :logic (n32 input-rflags)
			       :exec input-rflags))

	    (result  (mbe :logic
			  (n-size ,size (the (unsigned-byte ,size) (fast-rotate-right dst ,size src)))
			  :exec
			  (the (unsigned-byte ,size) (fast-rotate-right dst ,size src))))

	    ((mv (the (unsigned-byte 32) output-rflags)
		 (the (unsigned-byte 32) undefined-flags))

	     (case src
	       (0
		;; No flags, except OF, affected.
		(b* ((undefined-flags (the (unsigned-byte 32)
					(!rflags-slice :of 1 0))))

		  (mv input-rflags undefined-flags)))

	       (1
		;; CF and OF are the only affected flags.
		(b* ((cf
		      ;; CF = MSB of the  result.
		      (mbe :logic (logbit ,size-1 result)
			   :exec (logand 1
					 (the (unsigned-byte 1)
					   (ash (the (unsigned-byte ,size)
						  result)
						,neg-size-1)))))
		     (of
		      ;; OF = XOR of the two most significant bits of
		      ;; the result.
		      (b-xor (mbe :logic (logbit ,size-1 result)
				  :exec (logand 1
						(the (unsigned-byte 1)
						  (ash (the (unsigned-byte ,size)
							 result)
						       ,neg-size-1))))
			     (mbe :logic ;; (logbit ,size-2 result)
				  (part-select result :low ,size-2 :width 1)
				  :exec (logand 1
						(the (unsigned-byte 2)
						  (ash (the (unsigned-byte ,size)
							 result)
						       ,neg-size-2))))))
		     (output-rflags (the (unsigned-byte 32)
				      (!rflags-slice
				       :cf cf
				       (!rflags-slice
					:of of
					input-rflags)))))
		  (mv output-rflags 0)))

	       (otherwise
		;; CF is affected, OF is undefined.
		;; All other flags are unaffected.
		(b* ((cf ;; CF = MSB of the result.
		      (mbe :logic
			   (part-select result :low 0 :width 1)
			   :exec
			   (the (unsigned-byte 1)
			     (logand 1 (the (unsigned-byte ,size)
					 result)))))
		     (output-rflags (the (unsigned-byte 32)
				      (!rflags-slice
				       :cf cf
				       input-rflags)))

		     (undefined-flags (the (unsigned-byte 32)
					(!rflags-slice :of 1 0))))
		  (mv output-rflags undefined-flags)))))

	    (output-rflags (mbe :logic (n32 output-rflags)
				:exec output-rflags)))

	 (mv result output-rflags undefined-flags))

       ///

       (local (in-theory (e/d () (unsigned-byte-p))))

       (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	 :bound ,size
	 :concl (mv-nth 0 (,fn-name dst src input-rflags))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	 :bound 32
	 :concl (mv-nth 1 (,fn-name dst src input-rflags))
	 :gen-type t
	 :gen-linear t)

       (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	 :bound 32
	 :concl (mv-nth 2 (,fn-name dst src input-rflags))
	 :gen-type t
	 :gen-linear t))
    ))

(make-event (ror-spec-gen  8))
(make-event (ror-spec-gen 16))
(make-event (ror-spec-gen 32))
(make-event (ror-spec-gen 64))

(define ror-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (n06p src)
	      (case size
		(1 (n08p dst))
		(2 (n16p dst))
		(4 (n32p dst))
		(8 (n64p dst))
		(otherwise nil)))

  :inline t

  :parents (x86-instruction-semantics)

  :short "Specification for the @('ROR') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set
  Reference \(N-Z\).</p>

<p>For the ROR and ROR instructions, the orig- inal value of the CF
flag is not a part of the result, but the CF flag receives a copy of
the bit that was shifted from one end to the other. ... The OF flag is
defined only for the 1-bit rotates; it is undefined in all other cases
\(except RCL and RCR instructions only: a zero-bit rotate does
nothing, that is affects no flags\).  For right rotates, the OF flag
is set to the exclusive OR of the two most-significant bits of the
result.</p>"

  (case size
    (1 (ror-spec-8  dst src input-rflags))
    (2 (ror-spec-16 dst src input-rflags))
    (4 (ror-spec-32 dst src input-rflags))
    (8 (ror-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-ror-spec
    (natp (mv-nth 0 (ror-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-usb n32p-mv-nth-1-ror-spec
    :bound 32
    :concl (mv-nth 1 (ror-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mv-nth-2-ror-spec
    :bound 32
    :concl (mv-nth 2 (ror-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

;; ======================================================================

;; Shifts:

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local
 (defthm logbitp-and-logtail-thm
   (implies (and (bind-free
		  (list (list (cons 'n ''8))
			(list (cons 'n ''16))
			(list (cons 'n ''32))
			(list (cons 'n ''64)))
		  (n))
		 (natp dst)
		 (< dst (expt 2 n))
		 (natp n)
		 (natp m)
		 (< m n))
	    (equal (bool->bit (logbitp m dst))
		   (logand 1 (logtail m dst))))
   :hints (("Goal" :in-theory (e/d* (bool->bit
				     acl2::logtail**
				     acl2::ihsext-inductions
				     acl2::unsigned-byte-p**)
				    (unsigned-byte-p))))))

(local (in-theory (e/d (loghead-to-logand
			acl2::bitp)
		       (bitops::logand-with-bitmask))))

(define sal/shl-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (b* ((size-1 (1- size))
       (neg-size-1 (- size-1))
       (fn-name (mk-name "SAL/SHL-SPEC-" size))
       (?str-nbits (if (eql size 8) "08" size)))

      `(define ,fn-name
	 ((dst :type (unsigned-byte ,size))
	  (src :type (unsigned-byte 6)
	       "We assume @('src') has been masked appropriately by the decoding part of the shift instructions.")
	  (input-rflags :type (unsigned-byte 32)))

	 :parents (sal/shl-spec)

	 (b* ((dst (mbe :logic (n-size ,size dst)
			:exec dst))
	      (src (mbe :logic (n-size 6 src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))

	      (raw-result (ash dst src))
	      (result (the (unsigned-byte ,size) (n-size ,size raw-result)))

	      ((mv (the (unsigned-byte 32) output-rflags)
		   (the (unsigned-byte 32) undefined-flags))

	       (case src
		 (0
		  ;; No flags affected.
		  (mv input-rflags 0))

		 (1
		  ;; All flags, but AF, are changed accordingly. AF is
		  ;; undefined.
		  (b* ((cf
			;; CF contains the last bit shifted out of the operand.
			(mbe
			 :logic (part-select
				 dst
				 :low ,size-1 ;; (- ,size src)
				 :width 1)
			 :exec
			 (the (unsigned-byte 1)
			   (logand 1
				   (the (unsigned-byte ,size)
				     (ash (the (unsigned-byte ,size) dst)
					  ,neg-size-1))))))
		       (pf (general-pf-spec ,size result))
		       ;; AF is undefined.
		       (zf (zf-spec result))
		       (sf (general-sf-spec ,size result))
		       (of
			;; OF is set when the top two bits of the original
			;; operand are the same.
			(b-xor cf
			       (mbe :logic (logbit ,size-1 result)
				    :exec (the (unsigned-byte 1)
					    (logand 1
						    (the (unsigned-byte 1)
						      (ash (the (unsigned-byte ,size)
							     result)
							   ,neg-size-1)))))))

		       (output-rflags (the (unsigned-byte 32)
					(!rflags-slice
					 :cf cf
					 (!rflags-slice
					  :pf pf
					  (!rflags-slice
					   :zf zf
					   (!rflags-slice
					    :sf sf
					    (!rflags-slice
					     :of of
					     input-rflags)))))))

		       (undefined-flags (!rflags-slice :af 1 0)))

		      (mv output-rflags undefined-flags)))

		 (otherwise
		  (if (<= ,size src)
		      ;; CF is undefined for SHL and SHR where the src
		      ;; is >= the width of the destination operand. OF and
		      ;; AF are also undefined.  Other flags are affected as
		      ;; usual.
		      (b* ( ;; CF is undefined.
			   (pf (general-pf-spec ,size result))
			   ;; AF is undefined.
			   (zf (zf-spec result))
			   (sf (general-sf-spec ,size result))
			   ;; OF is undefined.

			   (output-rflags (the (unsigned-byte 32)
					    (!rflags-slice
					     :pf pf
					     (!rflags-slice
					      :zf zf
					      (!rflags-slice
					       :sf sf
					       input-rflags)))))

			   (undefined-flags (!rflags-slice
					     :cf 1
					     (!rflags-slice
					      :af 1
					      (!rflags-slice
					       :of 1 0)))))
			  (mv output-rflags undefined-flags))

		    ;; OF and AF are undefined. Other flags are affected as
		    ;; usual.
		    (b* ((cf
			  ;; CF contains the last bit shifted out
			  ;; of the operand.
			  (part-select dst :low (- ,size src) :width 1))
			 (pf (general-pf-spec ,size result))
			 ;; AF is undefined.
			 (zf (zf-spec result))
			 (sf (general-sf-spec ,size result))
			 ;; OF is undefined.

			 (output-rflags (the (unsigned-byte 32)
					  (!rflags-slice
					   :cf cf
					   (!rflags-slice
					    :pf pf
					    (!rflags-slice
					     :zf zf
					     (!rflags-slice
					      :sf sf
					      input-rflags))))))

			 (undefined-flags (!rflags-slice
					   :af 1
					   (!rflags-slice
					    :of 1 0))))
			(mv output-rflags undefined-flags))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      (undefined-flags (mbe :logic (n32 undefined-flags)
				    :exec undefined-flags)))

	     (mv result output-rflags undefined-flags))

	 ///

	 (local (in-theory (e/d () (unsigned-byte-p))))

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,size
	   :concl (mv-nth 0 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t))

      ))

(make-event (sal/shl-spec-gen  8))
(make-event (sal/shl-spec-gen 16))
(make-event (sal/shl-spec-gen 32))
(make-event (sal/shl-spec-gen 64))

(define sal/shl-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (n06p src)
	      (case size
		(1  (n08p dst))
		(2  (n16p dst))
		(4  (n32p dst))
		(8  (n64p dst))
		(otherwise nil)))

  :inline t

  :parents (x86-instruction-semantics)

  :short "Specification for the @('SAL/SHL') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set Reference
\(N-Z\).</p>

<p>The shift arithmetic left \(SAL\) and shift logical left \(SHL\)
instructions perform the same operation; they shift the bits in the
destination operand to the left \(toward more significant bit
locations\). For each shift count, the most significant bit of the
destination operand is shifted into the CF flag, and the least
significant bit is cleared.  The OF flag is affected only on 1-bit
shifts. For left shifts, the OF flag is set to 0 if the
most-significant bit of the result is the same as the CF flag (that
is, the top two bits of the original operand were the same);
otherwise, it is set to 1.</p>"

  (case size
    (1 (sal/shl-spec-8  dst src input-rflags))
    (2 (sal/shl-spec-16 dst src input-rflags))
    (4 (sal/shl-spec-32 dst src input-rflags))
    (8 (sal/shl-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-sal/shl-spec
    (natp (mv-nth 0 (sal/shl-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-usb n32p-mv-nth-1-sal/shl-spec
    :bound 32
    :concl (mv-nth 1 (sal/shl-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mv-nth-2-sal/shl-spec
    :bound 32
    :concl (mv-nth 2 (sal/shl-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

(define shr-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (b* ((size-1 (1- size))
       (size+1 (1+ size))
       (neg-size-1 (- size-1))
       (fn-name (mk-name "SHR-SPEC-" size))
       (?str-nbits (if (eql size 8) "08" size)))

      `(define ,fn-name
	 ((dst :type (unsigned-byte ,size))
	  (src :type (unsigned-byte 6)
	       "We assume @('src') has been masked appropriately by the decoding part of the shift instructions")
	  (input-rflags :type (unsigned-byte 32)))

	 :parents (shr-spec)

	 (b* ((dst (mbe :logic (n-size ,size dst)
			:exec dst))
	      (src (mbe :logic (n-size 6 src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))

	      (neg-src (the (signed-byte ,size+1) (- src)))
	      (raw-result (the (unsigned-byte ,size)
			    (ash
			     (the (unsigned-byte ,size) dst)
			     (the (signed-byte ,size+1) neg-src))))
	      (result (the (unsigned-byte ,size) (n-size ,size raw-result)))

	      ((mv (the (unsigned-byte 32) output-rflags)
		   (the (unsigned-byte 32) undefined-flags))

	       (case src
		 (0
		  ;; No flags affected.
		  (mv input-rflags 0))

		 (1
		  (b*
		   ((cf (mbe :logic (part-select dst :low 0 :width 1)
			     :exec (the (unsigned-byte 1)
				     (logand 1 (the (unsigned-byte ,size)
						 dst)))))
		    (pf (general-pf-spec ,size result))
		    ;; AF is undefined.
		    (zf (zf-spec result))
		    (sf (general-sf-spec ,size result))
		    (of (mbe :logic (part-select dst :low ,size-1 :width 1)
			     :exec  (the (unsigned-byte 1)
				      (ash (the (unsigned-byte ,size) dst)
					   ,neg-size-1))))

		    (output-rflags (the (unsigned-byte 32)
				     (!rflags-slice
				      :cf cf
				      (!rflags-slice
				       :pf pf
				       (!rflags-slice
					:zf zf
					(!rflags-slice
					 :sf sf
					 (!rflags-slice
					  :of of input-rflags)))))))
		    (undefined-flags (the (unsigned-byte 32)
				       (!rflags-slice :of 1 0))))
		   (mv output-rflags undefined-flags)))

		 (otherwise
		  (if (<= ,size src)
		      (b* (
			   ;; CF is undefined.
			   (pf (general-pf-spec ,size result))
			   ;; AF is undefined.
			   (zf (zf-spec result))
			   (sf (general-sf-spec ,size result))
			   ;; OF is undefined.
			   (output-rflags (the (unsigned-byte 32)
					    (!rflags-slice
					     :pf pf
					     (!rflags-slice
					      :zf zf
					      (!rflags-slice
					       :sf sf
					       input-rflags)))))

			   (undefined-flags (the (unsigned-byte 32)
					      (!rflags-slice
					       :cf 1
					       (!rflags-slice
						:af 1
						(!rflags-slice
						 :of 1 0))))))

			  (mv output-rflags undefined-flags))

		    (b* ((cf (mbe :logic (part-select dst :low (1- src) :width 1)
				  :exec (let* ((shft
						(the (signed-byte ,size)
						  (- 1
						     (the (unsigned-byte ,size) src)))))
					  (the (unsigned-byte 1)
					    (logand
					     1
					     (the (unsigned-byte ,size)
					       (ash
						(the (unsigned-byte ,size) dst)
						(the (signed-byte ,size) shft))))))))
			 (pf (general-pf-spec ,size result))
			 ;; AF is undefined.
			 (zf (zf-spec result))
			 (sf (general-sf-spec ,size result))
			 ;; OF is undefined.

			 (output-rflags (the (unsigned-byte 32)
					  (!rflags-slice
					   :cf cf
					   (!rflags-slice
					    :pf pf
					    (!rflags-slice
					     :zf zf
					     (!rflags-slice
					      :sf sf
					      input-rflags))))))

			 (undefined-flags (the (unsigned-byte 32)
					    (!rflags-slice
					     :af 1
					     (!rflags-slice
					      :of 1 0)))))
			(mv output-rflags undefined-flags))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      (undefined-flags (mbe :logic (n32 undefined-flags)
				    :exec undefined-flags)))

	     (mv result output-rflags undefined-flags))

	 ///

	 (local (in-theory (e/d () (unsigned-byte-p))))

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,size
	   :concl (mv-nth 0 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t))

      ))

(local
 (defthm logand-1-and-logtail-thm
   (implies (and (unsigned-byte-p (1+ n) dst)
		 (natp n))
	    (equal (logand 1 (logtail n dst))
		   (logtail n dst)))
   :hints (("Goal" :in-theory (e/d* (bool->bit
				     acl2::logtail**
				     acl2::ihsext-inductions
				     acl2::unsigned-byte-p**)
				    (unsigned-byte-p))))))

(make-event (shr-spec-gen  8))
(make-event (shr-spec-gen 16))
(make-event (shr-spec-gen 32))
(make-event (shr-spec-gen 64))

(define shr-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (unsigned-byte-p 6 src)
	      (case size
		(1 (n08p dst))
		(2 (n16p dst))
		(4 (n32p dst))
		(8 (n64p dst))
		(otherwise nil)))

  :inline t

  :parents (x86-instruction-semantics)

  :short "Specification for the @('SHR') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set Reference \(N-Z\).</p>

<p>The shift arithmetic right \(SAR\) and shift logical right \(SHR\)
instructions shift the bits of the destination operand to the right
\(toward less significant bit locations\). For each shift count, the
least significant bit of the destination operand is shifted into the
CF flag, and the most significant bit is either set or cleared
depending on the instruction type. The SHR instruction clears the most
significant bit (see Figure 7-8 in the Intel� 64 and IA-32
Architectures Software Developer s Manual, Volume 1)... The OF flag is
affected only on 1-bit shifts. For the SAR instruction, the OF flag is
cleared for all 1-bit shifts. For the SHR instruction, the OF flag is
set to the most-significant bit of the original operand.</p>"

  (case size
    (1 (shr-spec-8  dst src input-rflags))
    (2 (shr-spec-16 dst src input-rflags))
    (4 (shr-spec-32 dst src input-rflags))
    (8 (shr-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-shr-spec
    (natp (mv-nth 0 (shr-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-usb n32p-mv-nth-1-shr-spec
    :bound 32
    :concl (mv-nth 1 (shr-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mv-nth-2-shr-spec
    :bound 32
    :concl (mv-nth 2 (shr-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

(define sar-spec-gen ((size :type (member 8 16 32 64)))
  :verify-guards nil

  (b* ((size+1 (1+ size))
       (size-1 (1- size))
       (neg-size-1 (- size-1))
       (size-mask (1- (expt 2 size)))
       (fn-name (mk-name "SAR-SPEC-" size))
       (?str-nbits (if (eql size 8) "08" size)))

      `(define ,fn-name
	 ((dst :type (unsigned-byte ,size))
	  (src :type (unsigned-byte 6)
	       "We assume @('src') has been masked appropriately by the decoding part of the shift instructions")
	  (input-rflags :type (unsigned-byte 32)))

	 :parents (sar-spec)

	 (b* ((dst (mbe :logic (n-size ,size dst)
			:exec dst))
	      (src (mbe :logic (n-size 6 src)
			:exec src))
	      (input-rflags (mbe :logic (n32 input-rflags)
				 :exec input-rflags))

	      (neg-src (the (signed-byte ,size+1) (- src)))
	      (raw-result-not-sign-extended
	       (the (unsigned-byte ,size)
		 (ash
		  (the (unsigned-byte ,size) dst)
		  (the (signed-byte ,size+1) neg-src))))
	      (raw-result
	       (if (eql (mbe :logic (logbit ,size-1 dst)
			     :exec (logand 1
					   (the (unsigned-byte 1)
					     (ash (the (unsigned-byte ,size)
						    dst)
						  ,neg-size-1))))
			1)
		   (the (unsigned-byte ,size)
		     (logior ,size-mask raw-result-not-sign-extended))
		 raw-result-not-sign-extended))
	      (result (mbe :logic (n-size ,size raw-result)
			   :exec raw-result))

	      ((mv (the (unsigned-byte 32) output-rflags)
		   (the (unsigned-byte 32) undefined-flags))

	       (case src
		 (0
		  ;; No flags affected.
		  (mv input-rflags 0))

		 (1
		  (b*
		   ((cf (mbe :logic (part-select dst :low 0 :width 1)
			     :exec (the (unsigned-byte 1)
				     (logand 1 (the (unsigned-byte ,size)
						 dst)))))
		    (pf (general-pf-spec ,size result))
		    ;; AF is undefined.
		    (zf (zf-spec result))
		    (sf (general-sf-spec ,size result))
		    (of 0)

		    (output-rflags (the (unsigned-byte 32)
				     (!rflags-slice
				      :cf cf
				      (!rflags-slice
				       :pf pf
				       (!rflags-slice
					:zf zf
					(!rflags-slice
					 :sf sf
					 (!rflags-slice
					  :of of
					  input-rflags)))))))

		    (undefined-flags
		     (the (unsigned-byte 32)
		       (!rflags-slice :af 1 0))))
		   (mv output-rflags undefined-flags)))

		 (otherwise
		  (if (<= ,size src)
		      (b* (
			   ;; CF is undefined.
			   (pf (general-pf-spec ,size result))
			   ;; AF is undefined.
			   (zf (zf-spec result))
			   (sf (general-sf-spec ,size result))
			   ;; OF is undefined.
			   (output-rflags (the (unsigned-byte 32)
					    (!rflags-slice
					     :pf pf
					     (!rflags-slice
					      :zf zf
					      (!rflags-slice
					       :sf sf
					       input-rflags)))))

			   (undefined-flags (!rflags-slice
					     :cf 1
					     (!rflags-slice
					      :af 1
					      (!rflags-slice
					       :of 1 0)))))
			  (mv output-rflags undefined-flags))

		    (b* ((cf (mbe :logic (part-select dst :low (1- src) :width 1)
				  :exec (let* ((shft
						(the (signed-byte ,size)
						  (- 1
						     (the (unsigned-byte ,size) src)))))
					  (the (unsigned-byte 1)
					    (logand
					     1
					     (the (unsigned-byte ,size)
					       (ash
						(the (unsigned-byte ,size) dst)
						(the (signed-byte ,size) shft))))))))
			 (pf (general-pf-spec ,size result))
			 ;; AF is undefined.
			 (zf (zf-spec result))
			 (sf (general-sf-spec ,size result))
			 ;; OF is undefined.

			 (output-rflags (the (unsigned-byte 32)
					  (!rflags-slice
					   :cf cf
					   (!rflags-slice
					    :pf pf
					    (!rflags-slice
					     :zf zf
					     (!rflags-slice
					      :sf sf
					      input-rflags))))))

			 (undefined-flags (!rflags-slice
					   :af 1
					   (!rflags-slice
					    :of 1 0))))
			(mv output-rflags undefined-flags))))))

	      (output-rflags (mbe :logic (n32 output-rflags)
				  :exec output-rflags))

	      (undefined-flags (mbe :logic (n32 undefined-flags)
				    :exec undefined-flags)))

	     (mv result output-rflags undefined-flags))

	 ///

	 (local (in-theory (e/d () (unsigned-byte-p))))

	 (defthm-usb ,(mk-name "N" str-nbits "-MV-NTH-0-" fn-name)
	   :bound ,size
	   :concl (mv-nth 0 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-1-" fn-name)
	   :bound 32
	   :concl (mv-nth 1 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 (defthm-usb ,(mk-name "MV-NTH-2-" fn-name)
	   :bound 32
	   :concl (mv-nth 2 (,fn-name dst src input-rflags))
	   :gen-type t
	   :gen-linear t)

	 )))

(make-event (sar-spec-gen  8))
(make-event (sar-spec-gen 16))
(make-event (sar-spec-gen 32))
(make-event (sar-spec-gen 64))

(define sar-spec
  ((size   :type (member 1 2 4 8))
   dst src
   (input-rflags :type (unsigned-byte 32)))
  :guard (and (n06p src)
	      (case size
		(1 (n08p dst))
		(2 (n16p dst))
		(4 (n32p dst))
		(8 (n64p dst))
		(otherwise nil)))

  :inline t

  :parents (x86-instruction-semantics)

  :short "Specification for the @('SAR') instruction"

  :long "<p>Source: Intel Manual, Volume 2B, Instruction Set Reference \(N-Z\).</p>

<p>The shift arithmetic right \(SAR\) and shift logical right \(SHR\)
instructions shift the bits of the destination operand to the right
\(toward less significant bit locations\). For each shift count, the
least significant bit of the destination operand is shifted into the
CF flag, and the most significant bit is either set or cleared
depending on the instruction type.  The SAR instruction sets or clears
the most significant bit to correspond to the sign \(most significant
bit\) of the original value in the destination operand. In effect, the
SAR instruction fills the empty bit position s shifted value with the
sign of the unshifted value. ... The OF flag is affected only on 1-bit
shifts. For the SAR instruction, the OF flag is cleared for all 1-bit
shifts. For the SHR instruction, the OF flag is set to the
most-significant bit of the original operand.</p>"

  (case size
    (1 (sar-spec-8  dst src input-rflags))
    (2 (sar-spec-16 dst src input-rflags))
    (4 (sar-spec-32 dst src input-rflags))
    (8 (sar-spec-64 dst src input-rflags))
    (otherwise (mv 0 0 0)))

  ///

  (defthm natp-mv-nth-0-sar-spec
    (natp (mv-nth 0 (sar-spec size dst src input-rflags)))
    :rule-classes :type-prescription)

  (defthm-usb n32p-mv-nth-1-sar-spec
    :bound 32
    :concl (mv-nth 1 (sar-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t)

  (defthm-usb n32p-mv-nth-2-sar-spec
    :bound 32
    :concl (mv-nth 2 (sar-spec size dst src input-rflags))
    :gen-type t
    :gen-linear t))

;; ======================================================================
