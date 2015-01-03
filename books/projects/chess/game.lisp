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
(include-book "std/util/top" :dir :system)
(include-book "std/lists/top" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/vl/util/defoption" :dir :system)
(local (std::add-default-post-define-hook :fix))
(local (xdoc::set-default-parents game))

(defenum color-p
  (:black :white)
  :short "Color of a chess piece or a player.")

(defenum type-p
  (:pawn :rook :knight :bishop :queen :king)
  :short "Type of a single chess piece.")

(defprod piece
  :short "Representation of a single chess piece."
  ((color color-p "Color of this chess piece.")
   (type  type-p  "Kind of chess piece it is (king, queen, ...)")
   (moves natp    "How many times the piece has been moved."
          :rule-classes :type-prescription))
  :long "<p>It might seem strange to record the number of moves that each piece
has taken.  We do this so that we can tell whether <a
href='https://en.wikipedia.org/wiki/Castling'>castling</a> and <a
href='https://en.wikipedia.org/wiki/En_passant'>en passant</a> captures are
permitted.</p>")

(deflist piecelist :elt-type piece)

(defoption square-p piece-p
  :short "A square on the chess board may be occupied by a piece, or may be
nil to indicate that the square is blank.")

(deflist squarelist :elt-type square-p)

(define row-p (x)
  :short "A single row on the board is a list of 8 squares."
  (and (squarelist-p x)
       (eql (len x) 8))
  ///
  (defthm squarelist-p-when-row-p
    (implies (row-p x)
             (squarelist-p x))))

(define row-fix ((x row-p))
  :parents (row-p)
  :prepwork ((local (in-theory (enable row-p))))
  :returns (new-x row-p)
  :inline t
  (mbe :logic (if (row-p x)
                  x
                (squarelist-fix (take 8 x)))
       :exec x)
  ///
  (defthm row-fix-when-row-p
    (implies (row-p x)
             (equal (row-fix x)
                    x))))

(deffixtype row
  :pred row-p
  :fix row-fix
  :equiv row-equiv
  :define t)

(deflist rowlist :elt-type row
  ///
  (defthm squarelist-p-of-nth-when-rowlist-p
    (implies (rowlist-p x)
             (squarelist-p (nth n x)))))

(define board-p (x)
  :short "A board is a list of 8 rows."
  :long "<p>Rows in chess are often numbered from 1 to 8, but our rows go from
0 to 7 to agree with @(see nth).  We arbitrarily say that row 0 is the
\"bottom\" of the board and is initially the white side, and that row 7 is the
\"top\" of the board and it is initially the black side.</p>"
  (and (rowlist-p x)
       (eql (len x) 8))
  ///
  (defthm rowlist-p-when-board-p
    (implies (board-p x)
             (rowlist-p x)))
  (defthm board-p-of-rev
    (equal (board-p (rev x))
           (board-p x))))

(define board-fix ((x board-p))
  :parents (board-p)
  :prepwork ((local (in-theory (enable board-p))))
  :returns (new-x board-p)
  :inline t
  (mbe :logic (if (board-p x)
                  x
                (rowlist-fix (take 8 x)))
       :exec x)
  ///
  (defthm board-fix-when-board-p
    (implies (board-p x)
             (equal (board-fix x)
                    x))))

(deffixtype board
  :pred board-p
  :fix board-fix
  :equiv board-equiv
  :define t)

(defval *initial-board*
  :parents (board-p)
  :short "The starting configuration for the chess board."
  (b* ((wpawn   (make-piece :color :white :type :pawn   :moves 0))
       (wrook   (make-piece :color :white :type :rook   :moves 0))
       (wknight (make-piece :color :white :type :knight :moves 0))
       (wbishop (make-piece :color :white :type :bishop :moves 0))
       (wqueen  (make-piece :color :white :type :queen  :moves 0))
       (wking   (make-piece :color :white :type :king   :moves 0))
       (bpawn   (make-piece :color :black :type :pawn   :moves 0))
       (brook   (make-piece :color :black :type :rook   :moves 0))
       (bknight (make-piece :color :black :type :knight :moves 0))
       (bbishop (make-piece :color :black :type :bishop :moves 0))
       (bqueen  (make-piece :color :black :type :queen  :moves 0))
       (bking   (make-piece :color :black :type :king   :moves 0))
       (wback   (list wrook wknight wbishop wqueen wking wbishop wknight wrook))
       (bback   (list brook bknight bbishop bqueen bking bbishop bknight brook))
       (wpawns  (repeat 8 wpawn))
       (bpawns  (repeat 8 bpawn))
       (empty   (repeat 8 nil)))
    (list wback
          wpawns
          empty
          empty
          empty
          empty
          bpawns
          bback)))

(defprod game
  :short "Representation of the chess game state."
  ((board     board-p
              "The current game board with the locations of all the pieces.")
   (turn      color-p
              "Whose turn is it to go next?")
   ;; BOZO need some description of exactly which piece moved last, in order
   ;; to implement en passant moves.
   ))

(defval *initial-game*
  :short "The starting state of the chess game."
  (make-game :board    *initial-board*
             :turn     :white))

