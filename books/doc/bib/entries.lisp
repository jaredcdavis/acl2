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
(include-book "std/util/defalist" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/deflist-base" :dir :system)

(defsection entries
  :parents (bibtex)
  :short "A very basic, parsed representation of Bibtex entries.")

(local (set-default-parents entries))

(defalist bibdata-p (x)
  :key (keywordp x)
  :val (stringp x)
  :keyp-of-nil nil
  :valp-of-nil nil
  :short "Representation of the data for a single, parsed Bibtex entry."
  :long "<p>This is just an alist binding keywords to strings.  The idea
is that if we encounter a bibtex entry like</p>

@({
    @Book{00-kaufmann-car,
      author      = \"Matt Kaufmann and Panagiotis Manolios and J Strother Moore\",
      title       = \"Computer-Aided Reasoning: An Approach\",
      publisher   = \"Kluwer Academic Publishers\",
      month       = \"June\",
      year        = \"2000\",
      isbn        = \"978-0792377443\"
    }
})

<p>then we will convert the data for the entry into an alist like:</p>

@({
     ((:author    . \"Matt Kaufmann and Panagiotis Manolios and J Strother Moore\")
      (:title     . \"Computer-Aided Reasoning: An Approach\")
      (:publisher . \"Kluwer Academic Publishers\")
      (:month     . \"June\")
      (:year      . \"2000\")
      (:isbn      . \"978-0792377443\"))
})")

(defaggregate bibentry
  :tag :bibentry
  :short "Representation of a single bibtex entry."
  ((type keywordp
         "The kind of entry, e.g., for @('@Book{...}')  this will be
          @(':book'), for @('@Article{...}') it will be @(':article'), and so
          forth.")
   (id   stringp
         "The identifier for this entry, e.g., for @('@Book{00-kaufmann-car, 
         ...}') this would be @('\"00-kaufmann-car\"').")
   (data bibdata-p
         "The key/value bindings for the entry, e.g., this is where the
          author, title, etc., will be found.")))

(deflist bibentries-p (x)
  :short "Representation of a list of bibtex entries."
  (bibentry-p x)
  :elementp-of-nil nil)
