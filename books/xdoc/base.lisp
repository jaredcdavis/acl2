; XDOC Documentation System for ACL2
; Copyright (C) 2009-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

; base.lisp -- This file is only intended mainly to avoid a circular dependence
; between top.lisp and topics.lisp.  Ordinary users should include top.lisp
; instead.

(in-package "XDOC")
(set-state-ok t)

(table xdoc 'doc nil)
(table xdoc 'default-parents nil)
(table xdoc 'post-defxdoc-event nil)
(table xdoc 'resource-dirs nil)

(defun get-xdoc-table (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'doc (table-alist 'xdoc world))))

(defmacro set-default-parents (&rest parents)
  `(table xdoc 'default-parents
          (let ((parents ',parents))
            (cond ((symbol-listp parents)
                   parents)
                  ((and (consp parents)
                        (atom (cdr parents))
                        (symbol-listp (car parents)))
                   (car parents))
                  (t
                   (er hard? 'set-default-parents
                       "Expected a symbol-listp, but found ~x0" parents))))))

(defun get-default-parents (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'default-parents (table-alist 'xdoc world))))


(defun author-p (x)
  (declare (xargs :guard t))
  (or (stringp x)
      (and (true-listp x)
           (eql (len x) 3)
           (stringp (first x))
           (eql (second x) :for)
           (stringp (third x)))))

(defun authorlist-p (x)
  (declare (xargs :guard t))
  (if (atom x)
      (not x)
    (and (author-p (car x))
         (authorlist-p (cdr x)))))

(defmacro set-default-authors (&rest authors)
  `(table xdoc 'default-authors
          (let ((authors ',authors))
            (cond ((authorlist-p authors)
                   authors)
                  ((author-p authors)
                   (list authors))
                  (t
                   (er hard? 'set-default-authors
                       "Expected an author list but found ~x0" authors))))))

(defun get-default-authors (world)
  (declare (xargs :mode :program))
  (cdr (assoc-eq 'default-authors (table-alist 'xdoc world))))

(defun check-defxdoc-args (name parents authors short long)
  (declare (xargs :guard t))
  (or (and (not (symbolp name))
           "name is not a symbol!~%")
      (and (not (symbol-listp parents))
           ":parents are not a symbol list~%")
      (and (not (authorlist-p authors))
           ":authors are not a author list~%")
      (and short (not (stringp short))
           ":short is not a string (or nil)~%")
      (and long (not (stringp long))
           ":long is not a string (or nil)~%")))

(defun guard-for-defxdoc (name parents authors short long)
  (declare (xargs :guard t))
  (let* ((err (check-defxdoc-args name parents authors short long)))
    (or (not err)
        (cw err))))

(defun normalize-bookname (bookname state)
  (let* ((dir-system (acl2::f-get-global 'acl2::system-books-dir state))
         (lds        (length dir-system)))
    ;; Eventually we could do something fancier to support
    ;; add-include-book-dirs, but this is probably fine for the Community
    ;; Books, at least.
    (if (and (stringp dir-system)
             (stringp bookname)
             (<= lds (length bookname))
             (equal dir-system (subseq bookname 0 lds)))
        (concatenate 'string "[books]/"
                     (subseq bookname lds nil))
      bookname)))

(defun defxdoc-fn (name parents authors short long state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((err (check-defxdoc-args name parents authors short long)))
    (if err
        (er hard? 'defxdoc
            "Bad defxdoc arguments: ~s0" err)
      (let* ((world (w state))
             (pkg   (acl2::f-get-global 'acl2::current-package state))
             (info  (acl2::f-get-global 'acl2::certify-book-info state))
             (bookname (if info
                           (acl2::access acl2::certify-book-info info :full-book-name)
                         "Current Interactive Session"))
             (bookname (normalize-bookname bookname state))
             (parents (or parents (get-default-parents (w state))))
             (authors (or authors (get-default-authors (w state))))
             (entry (list (cons :name name)
                          (cons :base-pkg (acl2::pkg-witness pkg))
                          (cons :parents parents)
                          (cons :authors authors)
                          (cons :short short)
                          (cons :long long)
                          (cons :from bookname)))
             (table-event
              `(table xdoc 'doc
                      (cons ',entry (get-xdoc-table world))))
             (post-event
              (cdr (assoc-eq 'post-defxdoc-event (table-alist 'xdoc world)))))
        `(progn
           ,table-event
           ,@(and post-event (list post-event))
           (value-triple '(defxdoc ,name)))))))

(defmacro defxdoc (name &key parents authors short long)
  `(with-output :off (event summary)
     (make-event
      (defxdoc-fn ',name ',parents ',authors ,short ,long state))))

(defun defxdoc-raw-fn (name parents authors short long)
  (declare (xargs :guard t)
           (ignore name parents authors short long))
  (er hard? 'defxdoc-raw-fn
      "Under-the-hood definition of defxdoc-raw-fn not installed.  You ~
       probably need to load the defxdoc-raw book."))

(defun defxdoc-raw-after-check (name parents authors short long)
  (let* ((err (check-defxdoc-args name parents authors short long)))
    (if err
        (er hard? 'defxdoc-raw
            "Bad defxdoc-raw arguments: ~s0" err)
      (defxdoc-raw-fn name parents authors short long))))

(defmacro defxdoc-raw (name &key parents authors short long)
  `(defxdoc-raw-after-check ',name ',parents ',authors ,short ,long))

(defun find-topic (name x)
  (declare (xargs :mode :program))

; Look up a particular topic by name in the list of topics.

  (if (atom x)
      nil
    (if (equal (cdr (assoc :name (car x))) name)
        (car x)
      (find-topic name (cdr x)))))
