; Pretty Goals for ACL2
; Copyright (C) 2016 Kookamara LLC
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

(in-package "ACL2")

(defun prettyify-clause (cl let*-abstractionp wrld)
  (post-untranslate-hook

; We return an untranslated term that is equivalent to cl.  For a simpler
; function that returns a translated term, see prettyify-clause-simple.

  (if let*-abstractionp
      (mv-let (vars terms)
              (maximal-multiples (cons 'list cl) let*-abstractionp)
              (cond
               ((null vars)
                (prettyify-clause2 cl wrld))
               (t `(let* ,(listlis vars
                                   (untranslate-lst (all-but-last terms)
                                                    nil wrld))
                     ,(prettyify-clause2 (cdr (car (last terms))) wrld)))))
    (prettyify-clause2 cl wrld))))

