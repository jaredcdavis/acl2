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

#!ACL2
(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)

(defpkg "NATIVEARITH"
  (union-eq (set-difference-equal *standard-acl2-imports*
                                  '(apply eval bignum))
            (set-difference-equal std::*std-exports*
                                  '(std::deflist std::defalist))
            bitops::*bitops-exports*
            '(enable*
              disable*
              e/d*
              assert!
              maybe-natp
              lnfix
              b*
              fun
              why
              with-redef
              do-not
              bitops
              set-equiv
              two-nats-measure

              alist-keys
              alist-vals

              witness
              defquant
              defexample
              set-reasoning

              str::cat
              str::natstr

              a b c d e f g h i j k l m n o p q r s t u v w x y z
              pos size size1

              signed-byte-listp
              unsigned-byte-listp

              fty::deflist
              fty::defprod
              fty::deftypes
              fty::defalist
              fty::deftagsum
              fty::defflexsum
              fty::deffixtype
              fty::deffixequiv
              fty::deffixequiv-mutual
              )))

(assign acl2::verbose-theory-warning nil)
