; Chess in ACL2
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

(in-package "CHESS")
(include-book "game")
(include-book "std/strings/decimal" :dir :system)
(local (in-theory (disable character-listp)))
(local (std::add-default-post-define-hook :fix))

;; ANSI color codes for green, yellow, and reset.
(defconst *color-black* (implode (list (code-char 27) #\[ #\3 #\2 #\m)))
(defconst *color-white* (implode (list (code-char 27) #\[ #\3 #\4 #\m)))
(defconst *color-reset* (implode (list (code-char 27) #\[ #\0 #\m)))

; We could perhaps use Unicode characters for the chess pieces.  Unfortunately
; these don't seem to be the same width as regular characters, making it hard
; to draw a board that looks reasonable.  So for now I'll just stick with
; letters.

;; (defconst *white-king* (implode (list (code-char #xE2) (code-char #x99) (code-char #x94))))
;; (defconst *white-queen* (implode (list (code-char #xE2) (code-char #x99) (code-char #x95))))
;; (defconst *white-rook* (implode (list (code-char #xE2) (code-char #x99) (code-char #x96))))
;; (defconst *white-bishop* (implode (list (code-char #xE2) (code-char #x99) (code-char #x97))))
;; (defconst *white-knight* (implode (list (code-char #xE2) (code-char #x99) (code-char #x98))))
;; (defconst *white-pawn* (implode (list (code-char #xE2) (code-char #x99) (code-char #x99))))



;; Newline string
(defconst *nls* (implode (list #\Newline)))

(define ansi-piece ((x piece-p))
  :returns (str stringp :rule-classes :type-prescription)
  (b* (((piece x))
       (color (case x.color
                (:black *color-black*)
                (:white *color-white*)))
       (type  (case x.type
                (:pawn   "p")
                (:rook   "R")
                (:knight "N")
                (:bishop "B")
                (:queen  "Q")
                (:king   "K"))))
    (cat color type *color-reset*)))

(define ansi-square ((x square-p))
  :returns (str stringp :rule-classes :type-prescription)
  (b* ((x (square-fix x)))
    (if x
        (ansi-piece x)
      " ")))

(define ansi-squares ((x squarelist-p))
  :returns (str stringp :rule-classes :type-prescription)
  (if (atom x)
      ""
    (cat (ansi-square (car x))
         (if (consp (cdr x))
             " | "
           " |")
         (ansi-squares (cdr x)))))

(define ansi-rows ((x rowlist-p))
  :returns (str stringp :rule-classes :type-prescription)
  (if (atom x)
      ""
    (cat "  "
         (str::natstr (len x))
         " | "
         (ansi-squares (row-fix (car x)))
         " "
         (str::natstr (len x))
         *nls*
         (if (consp (cdr x))
             (cat "    |---+---+---+---+---+---+---+---|" *nls*)
           "")
         (ansi-rows (cdr x)))))

(define ansi-board ((x board-p))
  :returns (str stringp :rule-classes :type-prescription)
  (b* ((x (rev (board-fix x))))
    (cat
         "      a   b   c   d   e   f   g   h"   *nls*
         "    .-------------------------------," *nls*
         (ansi-rows x)
         "    `-------------------------------'" *nls*
         "      a   b   c   d   e   f   g   h"   *nls*
         *nls*)))

(define ansi-game ((x game-p))
  :returns (str stringp :rule-classes :type-prescription)
  :long "<p>Emacs users may need to turn @('font-lock-mode') off in their shell
buffer, and then @('M-x ansi-color-for-comint-mode-on').</p>"
  (b* (((game x)))
    (cat *nls*
         (ansi-board x.board)
         "    "
         (case x.turn
           (:white (cat *color-white* "White's Turn" *color-reset*))
           (:black (cat *color-black* "Black's Turn" *color-reset*)))
         ;; Could put other info down here, e.g., check, etc.
         ;; "     Kings Moved? "
         ;; *color-white* (if x.wkmovedp "y" "n") *color-reset*
         ;; "/"
         ;; *color-black* (if x.bkmovedp "y" "n") *color-reset*
         *nls*
         *nls*)))

#|

(princ$ (ansi-game *initial-game*) *standard-co* state)

|#
