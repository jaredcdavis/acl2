; An ACL2 Tarai Function book.
; Copyright (C) 2000  John R. Cowles, University of Wyoming

; This book is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This book is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this book; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:
; John Cowles
; Department of Computer Science
; University of Wyoming
; Laramie, WY 82071-3682 U.S.A.

;; The function Fb satisfies the tarai recursion and the
;;  restricted tarai recursion for lists of length 2-5.

;; (certify-book "C:/acl2/tak/tarai1")

(in-package "ACL2")

(defmacro
    last-el (lst)
    "Return the last element in the list lst."
    (list 'car (list 'last lst)))

(defun
    Gb (lst)
    "Bailey's g function for Knuth's Theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (cond ((consp (nthcdr 3 lst))    ;; (len lst) > 3
	   (if (or (equal (first lst)
			  (+ (second lst) 1))
		   (> (second lst)
		      (+ (third lst) 1)))
	       (Gb (rest lst))
	       (max (third lst)
		    (last-el lst))))
	  (t (last-el lst))))       ;; (len lst) <= 3


(defun
    decreasing-p (lst)
    "Determine if the elements in lst are strictly decreasing."
    (declare (xargs :guard (rational-listp lst)))
    (if (consp (rest lst))         ;; (len lst) > 1
	(and (> (first lst)(second lst))
	     (decreasing-p (rest lst)))
        t))

(defun
    first-non-decrease (lst)
    "Return the front of lst up to and including the first
     element that does not strictly decrease."
    (declare (xargs :guard (and (rational-listp lst)
				(not (decreasing-p lst)))))
    (if (consp (rest lst))        ;; (len lst) > 1
	(if (<= (first lst)(second lst))
	    (list (first lst)(second lst))
 	    (cons (first lst)
		  (first-non-decrease (rest lst))))
        lst))

(defun
    Fb (lst)
    "Bailey's f function for Knuth's theorem 4.
     The input lst is intended to be a nonempty
     list of integers."
    (declare (xargs :guard (and (integer-listp lst)
				(consp lst))))
    (if (decreasing-p lst)
	(first lst)
        (Gb (first-non-decrease lst))))

(defun
    rotate (lst)
    "Return the result of shifting the first element
     of the list lst onto the tail end of lst."
    (declare (xargs :guard (true-listp lst)))
    (if (consp lst)
	(append (rest lst)(list (first lst)))
        nil))

(defun
    minus-1 (lst)
    "Return the result of replacing (first lst)
     with (first lst) - 1."
    (declare (xargs :guard (and (rational-listp lst)
				(consp lst))))
    (if (consp lst)
	(cons (- (first lst) 1)
	      (rest lst))
        lst))

(defun
    lst-rotates-with-minus-1 (n lst)
    "Return the list of n+1 successive rotates of the 
     list lst with the first of each rotate replaced 
     by the first minus 1."
    (declare (xargs :guard (and (rational-listp lst)
				(consp lst)
				(integerp n)
				(>= n 0))))
    (if (zp n)
	(list (minus-1 lst))
        (cons (minus-1 lst)
	      (lst-rotates-with-minus-1 (- n 1)
					(rotate lst)))))

(defun
    Fb-lst (lst)
    (if (consp lst)
	(cons (Fb (first lst))
	      (Fb-lst (rest lst)))
        nil))

(defun
    dec-front-len (lst)
    "Return the number of strictly decreasing elements 
     at the front of the list lst."
    (declare (xargs :guard (rational-listp lst))) 
    (cond ((consp (rest lst))  ;; (len lst) > 1
	   (if (<= (first lst)(second lst))
	       1
	       (+ 1 (dec-front-len (rest lst)))))
	  ((consp lst) 1)      ;; (len lst) = 1
	  (t 0)))              ;; (len lst) = 0
;;------------------------------------------------------------
;; Fb satisfies the tarai recursion equation when lst is a
;;  true list of length 2:

(local
 (defthm
     lst-rotates-with-minus-1-2a
     (let ((lst (list first second)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second)
		    (list (- second 1) first))))
     :hints (("Goal"
	      :expand (lst-rotates-with-minus-1 
		       1 
		       (list first second))))))

(defthm 
    Fb-sat-tarai-def-2
    (let ((lst (list first second)))
      (equal (Fb lst)
	     (if (<= (first lst)
		     (second lst))
		 (second lst)
	       (Fb (Fb-lst (lst-rotates-with-minus-1 
			    (- (len lst) 1)
			    lst))))))
    :rule-classes nil)

(defthm
    Fb-sat-tarai-def-2a
    (let ((lst (list first second)))
      (equal (Fb lst)
	     (if (<= (first lst)
		     (second lst))
		 (second lst)
	       (Fb (Fb-lst (lst-rotates-with-minus-1 
			    (- (dec-front-len lst) 1)
			    lst))))))
    :rule-classes nil)
;----------------------------------------------------------
;; Fb satisfies the tarai recursion equation when lst is a
;;  true list of length 3:

(local
 (defthm
     lst-rotates-with-minus-1-3a
     (let ((lst (list first second third)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second third)
		    (list (- second 1) third first))))
     :hints (("Goal"
	      :expand ((lst-rotates-with-minus-1 
			1
			(list first second third)))))))

(local
 (defthm
     lst-rotates-with-minus-1-3b
     (let ((lst (list first second third)))
       (equal (lst-rotates-with-minus-1 2 lst)
	      (list (list (- first 1) second third)
		    (list (- second 1) third first)
		    (list (- third 1) first second))))))

(defthm
    Fb-sat-tarai-def-3
    (let ((lst (list first second third)))
      (equal (Fb lst)
	     (if (<= (first lst)
		     (second lst))
		 (second lst)
	       (Fb (Fb-lst (lst-rotates-with-minus-1 
			    (- (len lst) 1)
			    lst))))))
    :rule-classes nil)

(defthm  
    Fb-sat-tarai-def-3a
    (let ((lst (list first second third)))
      (equal (Fb lst)
	     (if (<= (first lst)
		     (second lst))
		 (second lst)
	       (Fb (Fb-lst (lst-rotates-with-minus-1 
			    (- (dec-front-len lst) 1)
			    lst))))))
    :rule-classes nil)
;;----------------------------------------------------------
;; Fb satisfies the tarai recursion equation when lst is a
;;  true list of length 4 whose last two elements are 
;;  acl2-numbers:

(local
 (defthm
     lst-rotates-with-minus-1-4a
     (let ((lst (list first second third forth)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second third forth)
		    (list (- second 1) third forth first))))
     :hints (("Goal"
	      :expand ((lst-rotates-with-minus-1 
			1
			(list first second third forth)))))))

(local
 (defthm
     lst-rotates-with-minus-1-4b
     (let ((lst (list first second third forth)))
       (equal (lst-rotates-with-minus-1 2 lst)
	      (list (list (- first 1) second third forth)
		    (list (- second 1) third forth first)
		    (list (- third 1) forth first second)))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-4c
     (let ((lst (list first second third forth)))
       (equal (lst-rotates-with-minus-1 3 lst)
	      (list (list (- first 1) second third forth)
		    (list (- second 1) third forth first)
		    (list (- third 1) forth first second)
		    (list (- forth 1) first second third)))))
 )

(defthm   
    Fb-sat-tarai-def-4
    (implies (and (acl2-numberp third)
		  (acl2-numberp forth))
	     (let ((lst (list first second third forth)))
	       (equal (Fb lst)
		      (if (<= (first lst)
			      (second lst))
			  (second lst)
			(Fb (Fb-lst (lst-rotates-with-minus-1 
				     (- (len lst) 1)
				     lst)))))))
    :rule-classes nil)

(defthm
    Fb-sat-tarai-def-4a
    (implies (and (acl2-numberp third)
		  (acl2-numberp forth))
	     (let ((lst (list first second third forth)))
	       (equal (Fb lst)
		      (if (<= (first lst)
			      (second lst))
			  (second lst)
			(Fb (Fb-lst (lst-rotates-with-minus-1 
				     (- (dec-front-len lst) 1)
				     lst)))))))
    :rule-classes nil)
;----------------------------------------------------------
;; Fb satisfies the tarai recursion equation when lst is a
;;  true list of integers of length 5.

(local
 (defthm
     lst-rotates-with-minus-1-5a
     (let ((lst (list first second third forth fifth)))
       (equal (lst-rotates-with-minus-1 1 lst)
	      (list (list (- first 1) second third forth fifth)
		    (list (- second 1) third forth fifth first))))
     :hints (("Goal"
	      :expand ((lst-rotates-with-minus-1 
			1
			(list first second third forth fifth))))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-5b
     (let ((lst (list first second third forth fifth)))
       (equal (lst-rotates-with-minus-1 2 lst)
	      (list (list (- first 1) second third forth fifth)
		    (list (- second 1) third forth fifth first)
		    (list (- third 1) forth fifth first second)))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-5c
     (let ((lst (list first second third forth fifth)))
       (equal (lst-rotates-with-minus-1 3 lst)
	      (list (list (- first 1) second third forth fifth)
		    (list (- second 1) third forth fifth first)
		    (list (- third 1) forth fifth first second)
		    (list (- forth 1) fifth first second third)))))
 )

(local
 (defthm
     lst-rotates-with-minus-1-5d
     (let ((lst (list first second third forth fifth)))
       (equal (lst-rotates-with-minus-1 4 lst)
	      (list (list (- first 1) second third forth fifth)
		    (list (- second 1) third forth fifth first)
		    (list (- third 1) forth fifth first second)
		    (list (- forth 1) fifth first second third)
		    (list (- fifth 1) first second third forth)
		    ))))
 )

(defthm
    Fb-sat-tarai-def-5
    (implies (and (integerp first)
		  (integerp second)
		  (integerp third)
		  (integerp forth)
		  (integerp fifth)
		  )
	     (let ((lst (list first second third forth fifth)))
	       (equal (Fb lst)
		      (if (<= (first lst)
			      (second lst))
			  (second lst)
			(Fb (Fb-lst (lst-rotates-with-minus-1 
				     (- (len lst) 1)
				     lst)))))))
    :rule-classes nil)

(defthm
    Fb-sat-tarai-def-5a
    (implies (and (integerp first)
		  (integerp second)
		  (integerp third)
		  (integerp forth)
		  (integerp fifth)
		  )
	     (let ((lst (list first second third forth fifth)))
	       (equal (Fb lst)
		      (if (<= (first lst)
			      (second lst))
			  (second lst)
			(Fb (Fb-lst (lst-rotates-with-minus-1 
				     (- (dec-front-len lst) 1)
				     lst)))))))
    :rule-classes nil)
