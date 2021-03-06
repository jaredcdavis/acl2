; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic 
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc. 
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful but WITHOUT ANY
; WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
; PARTICULAR PURPOSE.  See the GNU General Public License for more details.
;
; You should have received a copy of the GNU General Public License along with
; this program; see the file "gpl.txt" in this directory.  If not, write to the
; Free Software Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA
; 02110-1335, USA.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(set-enforce-redundancy t)

(include-book "../lib3/rtl")
(include-book "../lib3/arith")
(include-book "float") ;; Hack: we just definition of bits 

(local (include-book "../lib3/simplify-model-helpers"))

(defthm equal-log=-0
  (equal (equal (log= k x)
                0)
         (not (equal k x))))

(defthm equal-log=-1 ; possibly not needed
  (equal (equal (log= k x)
                1)
         (equal k x)))

(defthm equal-lnot-0
  (implies (bvecp x 1)
           (equal (equal (lnot x 1) 0)
                  (equal x 1))))

(defthm equal-lnot-1 ; possibly not needed
  (implies (bvecp x 1)
           (equal (equal (lnot x 1) 1)
                  (equal x 0))))

(defthm bits-if
  (equal (bits (if x y z) i j)
         (if x (bits y i j) (bits z i j))))

(defthm bitn-if
  (equal (bitn (if x y z) i)
         (if x (bitn y i) (bitn z i))))

(defthm bits-if1
  (equal (bits (if1 x y z) i j)
         (if1 x (bits y i j) (bits z i j))))

(defthm bitn-if1
  (equal (bitn (if1 x y z) i)
         (if1 x (bitn y i) (bitn z i))))

(defthm log=-0-rewrite
  (implies (bvecp k 1)
           (equal (log= 0 k)
                  (lnot k 1))))

(defthm log=-1-rewrite
  (implies (bvecp k 1)
           (equal (log= 1 k)
                  k)))

(defthm log<>-is-lnot-log=
  (equal (log<> x y) (lnot (log= x y) 1)))

(defthm cat-combine-constants
  (implies (and (syntaxp (and (quotep x)
                              (quotep m)
                              (quotep y)
                              (quotep n)))
                (equal (+ n p) r)
                (case-split (<= 0 m))
                (case-split (<= 0 n))
                (case-split (<= 0 p))
                (case-split (integerp m))
                (case-split (integerp n))
                (case-split (integerp p)))
           (equal (cat x m (cat y n z p) r)
                  (cat (cat x m y n) (+ m n) z p))))

(defthm bvecp-if
  (equal (bvecp (if test x y) k)
         (if test (bvecp x k) (bvecp y k))))

; bvecp-if1 is analogous to the above, and is already included in rtl.lisp

; Setbits can introduce a call of cat, which can introduce (bits (sig n) 2 0)
; say, even though sig is a single bit.  So we add the following.

(defthm cat-bitn-m-equal-cat-bitn-1
  (implies (and (syntaxp (and (quote m)
                              (natp (cadr m))
                              (> (cadr m) 1)))
                (natp m)
                (> m 1))
           (equal (cat (bitn x i) m y n)
                  (cat (bitn x i) 1 y n))))

;(in-theory (enable bvecp-monotone))
;(in-theory (enable bvecp-bits-0))

