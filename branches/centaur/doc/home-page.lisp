(in-package "ACL2")

(set-state-ok t)

(program)

(defun topic-to-url-list (url chars names)
; Url is a url ending in "/", e.g.,
; http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/ .
  (cond ((endp names) nil)
        (t (cons (cons (car chars)
                       (concatenate 'string
                                    url
                                    "index.html?topic=ACL2____"
                                    (symbol-name (car names))))
                 (topic-to-url-list url (cdr chars) (cdr names))))))

(defconst *acl2-user-manual*
  "manual/")

(defconst *combined-manual*
  "http://www.cs.utexas.edu/users/moore/acl2/current/combined-manual/")

(defconst *bleeding-edge-manual*
  "http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/")

(defconst *home-page-references*
  '(|The_02Tours|                       ;;; a
    ACL2-Tutorial                       ;;; b
    events                              ;;; c
    programming                         ;;; d
    rule-classes                        ;;; e
    books                               ;;; f
    note-6-3                            ;;; g   ; current release notes
    the-method                          ;;; h
    introduction-to-the-theorem-prover  ;;; i   ; This is not used right now.
    interesting-applications            ;;; j
    acknowledgments                     ;;; k
    real                                ;;; l
    hons-and-memoization                ;;; m
    parallelism                         ;;; n
    acl2-doc                            ;;; o
    acl2                                ;;; p
    |A_02Tiny_02Warning_02Sign|         ;;; q
  ))

(defconst *home-page*

; The numeric fmt variables used in the home page are resolved as follows:
; 0 (@ acl2-version)
; 1 *acl2-user-manual*
; 2 *combined-manual*
; 3 *bleeding-edge-manual*
; 4 build date month, e.g., "January"
; 5 build date day, e.g., 8
; 6 build date year, e.g., 1998

; Alphabetic fmt variables used below are defined in the defconst for
; *home-page-references*, immediately following the one for
; *home-page*.

          "~
<HTML>

<HEAD><TITLE>~s0</TITLE></HEAD>

<BODY TEXT=\"#000000\" BGCOLOR=\"#FFFFFF\">

<TABLE>
<TR>
<TD>
<IMG SRC=\"HTML/acl2-logo-200-134.gif\" ALIGN=LEFT ALT=\"ACL2\">
</TD>
<TD>
<CENTER><H1>~s0</H1></CENTER>

ACL2 is both a programming language in which you can model computer systems
and a tool to help you prove properties of those models.<P>

ACL2 is part of the Boyer-Moore family of provers, for which its authors have
received the 2005 <A HREF=\"http://awards.acm.org/software_system/\">ACM
Software System Award</A>.<P>

<TABLE BORDER=\"1\">
<TR>
<TD>
<a href=\"#search\"><font color=\"green\">SEARCH</font></a>
</TD>
</TR>
</TABLE>

</TD>
</TR>
</TABLE>
<HR>

<TABLE CELLPADDING=3>

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"~sa\"><IMG SRC=\"HTML/door02.gif\" BORDER=0></A>
</TD>
<TD>
Start Here: <A HREF=\"~sj\">Applications</A>, <A HREF=\"~sa\">Tours</A>, and <A HREF=\"~sb\">Tutorials/Demos</A>
</TD>

<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"http://www.cs.utexas.edu/users/moore/acl2/workshops.html\"><IMG SRC=\"HTML/teacher2.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"http://www.cs.utexas.edu/users/moore/acl2/workshops.html\">ACL2
Workshops, UT Seminar, and Course Materials</A>
</TD>
<!--

The Workshops entry was added in place of the FAQ entry.

The FAQ was added in place of the one removed by this comment.

At one time we had a link to the tutorials.  But after the publication
of the first book, we decided that we should encourage people to read the
book rather than do the tutorials, which are not elementary enough.
I think we should write some appropriate tutorials.  Meanwhile, this
entry is left blank.

<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"~sb\"><IMG SRC=\"HTML/teacher2.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"~sb\">Tutorials (for those who have taken the tours)</A>
</TD>
-->

</TR>

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html\">
<IMG SRC=\"HTML/doc03.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html\">
Publications about ACL2 and Its Applications</A>
</TD>

<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"#User's-Manual\"><IMG SRC=\"HTML/info04.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"#User's-Manual\">The User's Manual</A>
and <A HREF=\"http://www.cs.utexas.edu/users/moore/publications/hyper-card.html\">Hyper-Card</A>
</TD>
</TR>

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"#Tools\"><IMG SRC=\"HTML/tools3.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"#Tools\">Community Books: Lemma Libraries and Utilities</A>
</TD>

<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"HTML/installation/misc.html#Addresses\"><IMG SRC=\"HTML/mailbox1.gif\"  BORDER=0></A>
</TD>
<TD>
<A HREF=\"HTML/installation/misc.html#Addresses\">Mailing Lists</A>
</TD>
</TR>

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"HTML/new.html\">
<IMG SRC=\"HTML/new04.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"HTML/new.html\">
Recent changes to this page</A>
</TD>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"HTML/installation/installation.html\"><IMG SRC=\"HTML/ftp2.gif\"  BORDER=0></A>
</TD>
<TD>
<A HREF=\"HTML/installation/installation.html\">Obtaining, Installing, and License</A>
</TD>

</TR>

<TR>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"~sg\"><IMG SRC=\"HTML/note02.gif\" BORDER=0></A>
</TD>
<TD>
<A HREF=\"~sg\">Differences from Version 6.2</A><A HREF=\"~sq\"> <IMG
SRC=\"HTML/twarning.gif\"></A>
</TD>
<TD ALIGN=CENTER VALIGN=MIDDLE>
<A HREF=\"HTML/other-releases.html\">
<IMG SRC=\"HTML/file04.gif\"  BORDER=0></A>
</TD>
<TD>
<A HREF=\"HTML/other-releases.html\">
Other Releases</A>
</TD>
</TR>

</TABLE>

<BR>
<CENTER>
<B><A HREF=\"mailto:kaufmann@cs.utexas.edu\">Matt Kaufmann</A> and <A HREF=\"mailto:moore@cs.utexas.edu\">J Strother Moore</A></B><BR>
<A HREF=\"http://www.utexas.edu\">University of Texas at Austin</A><BR>
~s4 ~f5, ~f6
</CENTER>

<P>

<HR>

<p>

Welcome to the ACL2 home page!  We highlight a few aspects of ACL2:

<ul>

<li><b>Libraries (books).</b><br>Libraries of <i>books</i> (files containing
definitions and theorems) extend the code that we have written.  The <A
HREF=\"HTML/installation/installation.html\">installation instructions</A> explain
how to fetch the <i>community books</i>, which are contributed and maintained
by the members of the ACL2 community.  For more information, see the <code><A
HREF=\"http://acl2-books.googlecode.com/\">acl2-books</A></code> project
page.</li>

<li><b>Documentation.</b><br>There is an extensive user's manual for the ACL2
system, and an even more comprehensive manual that documents not only the ACL2
system but also many community books.  Follow <A HREF=\"#User's-Manual\">this
link</A> to learn more.</li>

<li><a name=\"bleeding-edge\"><b>Bleeding-edge distributions.</b></a><br>The
libraries and the ACL2 source code are under revision control, using svn.
Thus, versions of ACL2 and the libraries are available between ACL2 releases.
<i>The authors of ACL2 consider svn distributions to be experimental; while
they will likely be fully functional in most cases, they could however be
incomplete, fragile, and unable to pass our own regression.</i> If you decide
to use svn versions of either the libraries or ACL2, then you should use both,
as they tend to be kept in sync.  See the project websites, <code><A
HREF=\"http://acl2-books.googlecode.com/\">acl2-books</A></code> and <code><A
HREF=\"http://acl2-devel.googlecode.com/\">acl2-devel</A></code>, for the ACL2
libraries and development sources, respectively.</li>

<li><b>Extensions.</b><br>The ACL2 distribution includes the following
extensions, which were developed by the individuals shown.
  <UL>
  <LI><A HREF=\"~sl\">ACL2(r)</A><BR>
  Support for the real numbers by way of non-standard analysis<BR>
  Ruben Gamboa</LI>
  <LI><A HREF=\"~sm\">ACL2(h)</A><BR>
  Support for hash cons, applicative hash tables, and function
    memoization for reuse of previously computed results<BR>
  Bob Boyer, Warren A. Hunt, Jr., Jared Davis, and Sol Swords</LI>
  <LI><A HREF=\"~sn\">ACL2(p)</A><BR>
  Support for parallel evaluation<BR>
  David L. Rager</LI>
  </UL>

Another extension of ACL2 is the Eclipse-based <A
HREF=\"http://acl2s.ccs.neu.edu/acl2s/doc/\">ACL2 Sedan</A> (ACL2s).  Unlike
the systems above, ACL2s is distributed and maintained by Pete Manolios and his
research group.  ACL2s comes with a standard executable ACL2 image for Windows,
but it also comes with pre-certified community books and an extension of ACL2
with additional features, including extra automation for termination proofs as
well as counterexample generation.

</UL>

<HR>

<BR>
We gratefully acknowledge substantial support from the following.  (These are
included in a much more complete <A href=\"~sk\">acknowledgments page</A>.)
<UL>
<LI>DARPA</LI>
<LI>National Science Foundation
  <UL>
  <LI>This material is based upon work supported by the National Science
      Foundation under Grant Nos. EIA-0303609, CNS-0429591, ISS-0417413,
      CCF-0945316, and CNS-0910913.</LI>
  <LI>Any opinions, findings and conclusions or recomendations expressed in
      this material are those of the authors and do not necessarily reflect the
      views of the National Science Foundation.</LI>
  </UL></LI>
<LI>Advanced Micro Devices, Inc.</LI>
<LI>ForrestHunt, Inc.</LI>
<LI>Rockwell Collins, Inc.</LI>
<LI>Sun Microsystems, Inc.</LI>
</UL>

<HR>

<H2><A NAME=\"User's-Manual\">The User's Manual</A></H2>

ACL2's user manual is a vast hypertext document.  If you are a newcomer to
ACL2, we do <EM>not</EM> recommend that you wander off into the full
documentation.  Instead start with the <A HREF=\"~sb\">ACL2-TUTORIAL</A>
documentation topic.  Experienced users tend mostly to use the manual as a
reference manual, to look up concepts mentioned in error messages or vaguely
remembered from their past experiences with ACL2.

<P>

The documentation is available for reading in a Web browser, in the <A
HREF=\"~so\">ACL2-Doc Emacs browser</A>, and by using the ACL2
<CODE>:DOC</CODE> command at the terminal.  You will probably want to view the
<i>ACL2+books combined manual</i>, which includes documentation for not only
the ACL2 system but also for many of the <A href=\"#Tools\">community
books</A> (libraries); but an ACL2-only manual is also available.  Here are
links to those manuals on the web; also see the <A HREF=\"~so\">documentation
for the ACL2-Doc Emacs browser</A>, if you want to view either of those two
manuals in Emacs.

<ul>

<li><A HREF=\"~sp\">ACL2 user manual</A></li>

<li><A HREF=\"~s2\">ACL2+books combined manual</A></li>

<li><A HREF=\"~s3\">ACL2+books combined manual</A> for
\"<A HREF=\"#bleeding-edge\">bleeding edge</A>\" distributions</li>

</ul>

<P>

You can build local copies of the manuals from the ACL2 community
books, following instructions in <code>books/GNUmakefile</code>.

<BR><HR><BR>
<H2><A NAME=\"Tools\">Community Books: Lemma Libraries and Utilities, and How to Contribute</A></H2>

A companion to ACL2 is the library of <em>community books</em>, which have
been developed by many users over the years.  These books contain definitions
and theorems that you might find useful in your models and proofs.  In
addition, some books contain ACL2 reasoning or analysis tools built by users.
The <A HREF=\"HTML/installation/installation.html\">installation instructions</A>
explain how to <A
HREF=\"http://code.google.com/p/acl2-books/downloads/\">download</A> and
install the community books.

<p>

We strongly encourage users to submit additional books or improve existing
books, by following the instructions at the acl2-books project page hosted at
<code><A
HREF=\"http://acl2-books.googlecode.com/\">http://acl2-books.googlecode.com</a></code>.
In particular, the community book <code>books/system/doc/acl2-doc.lisp</code>
contains the ACL2 system documentation.  Members of the acl2-books project are
welcome to edit that book in order to improve the system documentation.

<p>

We also distribute a few interface
tools.  For these, see the <A
HREF=\"http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html#Utilities\">Utilities</A>
section of <A HREF=
\"http://www.cs.utexas.edu/users/moore/publications/acl2-papers.html\">
Books and Papers about ACL2 and Its Applications</A>.  Some of the
papers mentioned in that collection contain utilities, scripts, or
ACL2 books for the problem domains in question.

<H2><A NAME=\"search\">Searching documentation and books</A></H2>

The links below may help you to search the ACL2 documentation and the ACL2
community books, respectively.  Our approach is low-tech, but intended to be
reliable and easy to use on any platform.  You might want to add a bookmark for
each of these.

<ul>

<li>
The following link will take you to a search box on a Google page,
which has the following contents.
<pre>
search_term site:http://www.cs.utexas.edu/users/moore/acl2/v6-3
</pre>
Now simply replace the word `search_term' with your topic.  For example, replace
`<code>search_term</code>' by `<code>tail recursion</code>' to get
documentation about tail recursion.
<pre>
tail recursion site:http://www.cs.utexas.edu/users/moore/acl2/v6-3
</pre>
Now you are ready to follow the link.
<p>
<a href=\"http://www.google.com/search?q=search_term
                 site:http://www.cs.utexas.edu/users/moore/acl2/v6-3\">SEARCH
                 THE DOCUMENTATION</a>
</li>

<p>

<li>

The next link will take you to the community books website (which is external
to the present ACL2 website), specifically to the section entitled ``Searching
and browsing the books.''  There, you will see a search box in which you can
enter your search term.  For example, if you type `<code>tail recursion</code>'
and then <code>&lt;RETURN&gt;</code>, you will see text from several books in
the svn trunk that deal with the topic of tail recursion, with an
accompanying <i>``File Path''</i> shown at the end of each book's text.

<p>

<a
  href=\"https://code.google.com/p/acl2-books/#Searching_and_browsing_the_books\">SEARCH
  THE COMMUNITY BOOKS</a></a><br>

</li>

</ul>

<BR><HR><BR><BR><BR><BR><BR><BR>
<BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR>
<BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR>
<BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR>
<BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR><BR>

</BODY>
</HTML>
")

(defun write-home-page (channel state url)

; Url is a url ending in "/", e.g.,
; http://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/ .

  (mv-let
   (n state)
   (read-idate state)
   (let* ((date-list (decode-idate n))
          (day (cadddr date-list))
          (month (nth (1- (car (cddddr date-list)))
                      '("January" "February" "March" "April" "May"
                        "June" "July" "August" "September" "October"
                        "November" "December")))
          (yr (+ 1900 (cadr (cddddr date-list)))))
     (pprogn
      (fms
       *home-page*
       (append
        (list (cons #\0 (f-get-global 'acl2-version state))
              (cons #\1 *acl2-user-manual*)
              (cons #\2 *combined-manual*)
              (cons #\3 *bleeding-edge-manual*)
              (cons #\4 month)
              (cons #\5 day)
              (cons #\6 yr))
        (topic-to-url-list
         url
         '(#\a #\b #\c #\d #\e #\f #\g #\h #\i #\j #\k #\l #\m
           #\n #\o #\p #\q #\r #\s #\t #\u #\v #\w #\x #\y #\z
           #\A #\B #\C #\D #\E #\F #\G #\H #\I #\J #\K #\L #\M
           #\N #\O #\P #\Q #\R #\S #\T #\U #\V #\W #\X #\Y #\Z)
         *home-page-references*))
       channel
       state
       nil)
      (newline channel state)))))

(defmacro write-home-page-top ()
  '(mv-let (channel state)
           (open-output-channel "home-page.html" :character state)
           (pprogn (set-fmt-hard-right-margin 10000 state)
                   (set-fmt-soft-right-margin 10000 state)
                   (observation 'top-level "Writing home-page.html.")
                   (write-home-page channel state *acl2-user-manual*)
                   (close-output-channel channel state))))

;; Deleted *home-page* and *home-page-references* from ld.lisp.
