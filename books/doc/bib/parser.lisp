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
(include-book "entries")
(include-book "centaur/clex/top" :dir :system)
(include-book "std/strings/top" :dir :system)
(local (include-book "local"))

(defsection parser
  :parents (bibtex)
  :short "A basic Bibtex parser."

  :long "<p>This is a very basic parser for converting Bibtex files into a list
of @(see entries) that we can easily load into @(see xdoc::xdoc) or process in
other ways.  The parser can load a load files into lists of @(see bibentry-p)
structures.</p>")

(local (set-default-parents parser))

(defcharset whitespace
  (or (eql x #\Space)
      (eql x #\Newline)
      (eql x #\Tab)
      (eql (char-code x) 13) ;; carriage return
      (eql (char-code x) 12) ;; form feed
      (eql (char-code x) 11) ;; vertical tab
      )
  :short "Recognize basic whitespace.")

(defcharset letter
  (let ((code (char-code x)))
    (or (and (<= (char-code #\a) code)
             (<= code (char-code #\z)))
        (and (<= (char-code #\A) code)
             (<= code (char-code #\Z)))))
  :short "Recognize alphabetic characters, upper or lower case.")

(define skip-whitespace (sin)
  :short "Skip past and ignore any whitespace."
  :returns sin
  (b* (((mv ?match sin)
        (sin-match-charset* (whitespace-chars) sin)))
    sin)
  ///
  (defthm skip-whitespace-progress
    (<= (len (strin-left (skip-whitespace sin)))
        (len (strin-left sin)))
    :rule-classes ((:rewrite) (:linear))))

(define match-@foo (sin)
  :short "Recognize the start of an entry, e.g., @('@Book'), @('@Article'), etc."
  :returns (mv (foo (iff (keywordp foo) foo))
               (sin))
  (b* (((when (sin-endp sin))
        (mv nil sin))
       (car (sin-car sin))
       ((unless (eql car #\@))
        (mv nil sin))
       ((mv body sin) (sin-match-charset* (letter-chars) sin))
       ((unless body)
        (mv nil sin)))
    (mv (intern$ (str::upcase-string body) "KEYWORD")
        sin))
  ///
  (def-sin-progress match-@foo :hyp foo)
  (more-returns
   (foo symbolp :rule-classes :type-prescription)))

zz

(define 

http://thedailyshow.cc.com/full-episodes/tc3345/october-27--2014---wendy-davis



