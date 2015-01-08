; ACL2 Bibliography
; Copyright (C) 2014 Kookamara LLC
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

(in-package "BIB")
(include-book "xdoc/top" :dir :system)

(defsection keywordp-of-intern

  (local (defthm l0
           (iff (member-symbol-name str nil)
                nil)
           :hints(("Goal" :in-theory (enable member-symbol-name)))))

  (local (defthm l1
           (implies (stringp x)
                    (equal (symbol-package-name (intern-in-package-of-symbol x :acl2-pkg-witness))
                           "KEYWORD"))))

  (local (defthm l2
           (implies (not (stringp x))
                    (equal (intern-in-package-of-symbol x y)
                           nil))))

  (defthm symbol-package-name-of-intern-into-keyword-package
    (equal (symbol-package-name (intern-in-package-of-symbol x :acl2-pkg-witness))
           (if (stringp x)
               "KEYWORD"
             (symbol-package-name nil))))

  (defthm keywordp-of-intern-into-keyword-package
    (equal (keywordp (intern-in-package-of-symbol x :acl2-pkg-witness))
           (stringp x)))

  (local (defthm l3
           (implies (stringp x)
                    (intern-in-package-of-symbol x :acl2-pkg-witness))
           :hints(("Goal"
                   :in-theory (disable symbol-package-name-of-intern-into-keyword-package)
                   :use ((:instance symbol-package-name-of-intern-into-keyword-package))))))

  (defthm intern-into-keyword-package-under-iff
    (iff (intern-in-package-of-symbol x :acl2-pkg-witness)
         (stringp x))))
