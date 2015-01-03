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
(include-book "lists")
(local (std::add-default-post-define-hook :fix))

(defxdoc moves
  :short "Definition of legal moves.")

(local (xdoc::set-default-parents moves))

(define coordinate-p (x)
  (and (natp x)
       (< x 8))
  ///
  (defthm natp-when-coordinate-p
    (implies (coordinate-p x)
             (natp x))))

(define coordinate-fix ((x coordinate-p))
  :returns (coord coordinate-p)
  :inline t
  :prepwork ((local (in-theory (enable coordinate-p))))
  (mbe :logic (if (coordinate-p x)
                  x
                0)
       :exec x)
  ///
  (defthm coordinate-fix-of-coordinate-p
    (implies (coordinate-p x)
             (equal (coordinate-fix x)
                    x))))

(deffixtype coordinate
  :pred coordinate-p
  :fix coordinate-fix
  :equiv coordinate-equiv
  :define t)

(defprod location
  ((row coordinate-p)
   (col coordinate-p))
  ///
  (defthm natp-of-location->row
    (natp (location->row x))
    :rule-classes :type-prescription)
  (defthm natp-of-location->col
    (natp (location->col x))
    :rule-classes :type-prescription))

(defsection get/set-square

  (local (defthm row-p-of-nth
           (implies (and (board-p board)
                         (coordinate-p row))
                    (row-p (nth row board)))
           :hints(("Goal" :in-theory (enable board-p coordinate-p)))))

  (local (defthm square-p-of-nth
           (implies (and (row-p row)
                         (coordinate-p col))
                    (square-p (nth col row)))
           :hints(("Goal" :in-theory (enable row-p coordinate-p)))))

  (local (defthm row-p-of-update-nth
           (implies (and (force (row-p row))
                         (force (square-p val))
                         (force (coordinate-p col)))
                    (row-p (update-nth col val row)))
           :hints(("Goal" :in-theory (enable row-p coordinate-p)))))

  (local (defthm board-p-of-update-nth
           (implies (and (force (board-p board))
                         (force (row-p val))
                         (force (coordinate-p row)))
                    (board-p (update-nth row val board)))
           :hints(("Goal" :in-theory (enable board-p coordinate-p)))))

  (define get-square ((loc   location-p)
                      (board board-p))
    :returns (square square-p)
    :short "Get the square at @('board[loc]')."
    (b* ((board (board-fix board))
         ((location loc)))
      (nth-loose loc.col (nth-loose loc.row board))))

  (define set-square ((loc   location-p)
                      (val   square-p)
                      (board board-p))
    :returns (new-board board-p)
    :short "Set the square at @('board[loc]') to @('val')."
    (b* ((board (board-fix board))
         (val   (square-fix val))
         ((location loc))
         (old-row (nth-loose loc.row board))
         (new-row (update-nth-loose loc.col val old-row)))
      (update-nth-loose loc.row new-row board)))

  (local (in-theory (enable get-square set-square)))

  (defthm get-square-of-set-square-same
    (equal (get-square loc (set-square loc val board))
           (square-fix val)))

  (defthm set-square-of-set-square-same
    (equal (set-square loc1 val1 (set-square loc1 val2 board))
           (set-square loc1 val1 board)))

  (local (defthm crock
           (equal (location-equiv x y)
                  (and (equal (location->row x) (location->row y))
                       (equal (location->col x) (location->col y))))
           :hints(("Goal" :in-theory (enable location-equiv
                                             location-fix
                                             location->row
                                             location->col)))))

  (local (defthm crock2
           (equal (equal (location-fix x) (location-fix y))
                  (and (equal (location->row x) (location->row y))
                       (equal (location->col x) (location->col y))))
           :hints(("Goal" :use ((:instance crock))))))

  (local (in-theory (disable acl2::update-nth-when-zp
                             acl2::update-nth-of-cons
                             acl2::nth-when-zp)))

  (defthm set-square-of-set-square-diff
    (implies (not (location-equiv loc1 loc2))
             (equal (set-square loc1 val1 (set-square loc2 val2 board))
                    (set-square loc2 val2 (set-square loc1 val1 board))))
    :rule-classes ((:rewrite :loop-stopper ((loc1 loc2 set-square))))
    :hints(("Goal"
            :cases ((equal (location->col loc1) (location->col loc2))
                    (equal (location->row loc1) (location->row loc2))))))

  (local (defthm l0
           (implies (and (row-p row)
                         (coordinate-p n))
                    (equal (update-nth n (nth n row) row)
                           (row-fix row)))
           :hints(("Goal" :in-theory (enable coordinate-p row-p)))))

  (local (defthm l1
           (implies (and (board-p board)
                         (coordinate-p n))
                    (equal (update-nth n (nth n board) board)
                           (board-fix board)))
           :hints(("Goal" :in-theory (enable coordinate-p board-p)))))

  (defthm set-square-of-get-square-same
    (equal (set-square loc1 (get-square loc1 board) board)
           (board-fix board))))


(deftagsum move
  (:normal
   :short "Ordinary moves and also en passant captures."
   ((from    location-p   "Location to move from.")
    (to      location-p   "Location to move to.")))
  (:promote
   :short "Pawn promotion move."
   ((from    location-p   "Location to move from.")
    (to      location-p   "Location to move to.")
    (newtype type-p
             "Type of piece to promote to.  It's not legal to promote to a pawn
              or a king, but we don't enforce that in the type itself.")))
  (:castle
   :short "Castling move."
   ((king    location-p   "Starting location of the king.")
    (rook    location-p   "Starting location of the rook to castle with."))))

(define move-normal-basic-okp ((move move-p) (board board-p))
  :short "Basic criteria required of all normal moves."
  :long "<p>We check that the starting square refers to a piece, and that the
ending square isn't a piece of the same color.</p>"
  :guard (equal (move-kind move) :normal)
  (b* (((move-normal move))
       (start (get-square move.from board))
       (end   (get-square move.to   board)))
    (and start
         (type-equiv (piece->type start) :knight)
         (or (not end)
             (not (color-equiv (piece->color start)
                               (piece->color end)))))))


(define rookly-motion-p ((move move-p))
  :short "Rooks move in straight lines."
  :guard (equal (move-kind move) :normal)
  (b* (((move-normal move))
       ((location move.from))
       ((location move.to))
       (row-dist (abs (- move.from.row move.to.row)))
       (col-dist (abs (- move.from.col move.to.col))))
    (or (and (posp row-dist) (zp col-dist))
        (and (posp col-dist) (zp row-dist)))))

(define knightly-motion-p ((move move-p))
  :short "Knights move in an ``L'' shape."
  :guard (equal (move-kind move) :normal)
  (b* (((move-normal move))
       ((location move.from))
       ((location move.to))
       (row-dist (abs (- move.from.row move.to.row)))
       (col-dist (abs (- move.from.col move.to.col))))
    (or (and (eql row-dist 2)
             (eql col-dist 1))
        (and (eql row-dist 1)
             (eql col-dist 2)))))

(define bishoply-motion-p ((move move-p))
  :short "Bishops move in a diagonal line."
  :guard (equal (move-kind move) :normal)
  (b* (((move-normal move))
       ((location move.from))
       ((location move.to))
       (row-dist (abs (- move.from.row move.to.row)))
       (col-dist (abs (- move.from.col move.to.col))))
    (and (posp row-dist)
         (eql row-dist col-dist))))

(define queenly-motion-p ((move move-p))
  :short "Queens move in straight or diagonal lines."
  :guard (equal (move-kind move) :normal)
  (b* (((move-normal move))
       ((location move.from))
       ((location move.to))
       (row-dist (abs (- move.from.row move.to.row)))
       (col-dist (abs (- move.from.col move.to.col))))
    (and (posp row-dist)
         (eql row-dist col-dist))))

(define kingly-motion-p ((move move-p))
  :short "Kings move one space in any direction (for normal moves, ignoring castling)."
  :guard (equal (move-kind move) :normal)
  (b* (((move-normal move))
       ((location move.from))
       ((location move.to))
       (row-dist (abs (- move.from.row move.to.row)))
       (col-dist (abs (- move.from.col move.to.col))))
    (and (<= row-dist 1)
         (<= col-dist 1)
         (not (and (zp row-dist)
                   (zp col-dist))))))



(define slice-row
  :short "Extract squares from row[start..end)."
  ((row   coordinate-p "Row to extract squares from.")
   (start coordinate-p "Starting column")
   (end   coordinate-p "Ending column")
   (board board-p))
  :guard   (<= start end)
  :returns (squares squarelist-p)
  :measure (nfix (- (coordinate-fix end) (coordinate-fix start)))
  (b* ((start (coordinate-fix start))
       (end   (coordinate-fix end))
       ((when (zp (- end start)))
        nil))
    (cons (get-square (make-location :row row :col start) board)
          (slice-row row (+ 1 start) end board))))
         
                   


  (if (zp 


(define collect-pieces-in-line ((start location-p)
                                (end   location-p)

  :guard (
                         
  :guard (equal (move-kind move) :normal)

  


(define pawnly-motion-type ((move move-p))
  :short "Pawns move one or two spaces to open, or one space forward or
forward-diagonal (when attacking)."
  :guard (equal (move-kind move) :normal)
  (b* (((move-normal move))
       ((location move.from))
       ((location move.to))
       (row-dist (abs (- move.from.row move.to.row)))
       (col-dist (abs (- move.from.col move.to.col))))
    (and (<= row-dist 1)
         (<= col-dist 1)
         (not (and (zp row-dist)
                   (zp col-dist))))))
  
  
  
  



(define move-normal-pawn-shape-p ((move move-p))
  


(define move-okp ((move move-p)
                  (board board-p))
  :returns (okp booleanp :rule-classes :type-prescription)
  :short "Check if a move is ok (ignoring whose turn it is)."
  (b* (((move move))
    
  
