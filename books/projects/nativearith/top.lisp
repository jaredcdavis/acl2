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

(in-package "NATIVEARITH")
(include-book "smallops")
(include-book "smallexpr")
(include-book "smalleval")
(include-book "bigint")
(include-book "bigops")
(include-book "bigexpr")
(include-book "bigeval")
(include-book "llvm/ops")
(include-book "llvm/opstest")


(defxdoc nativearith
  :short "A library of ``native'' machine-like arithmetic expressions with a
strong connection to <a href='http://llvm.org/'>LLVM</a> assembly code."

  :long "<h3>Overview</h3>

<p>This work is exploratory prototyping.  Our short-term goal is to develop a
very fast way to execute @(see sv::svex) expressions.</p>

<h5>Small Operations and Expressions</h5>

<p>We define a simple expression format; see @(see smallexpr).  These
expressions consist of constants, variables, and applications of certain,
pre-defined @(see operations) which are styled after ``native'' machine
arithmetic operations&mdash;bitwise AND/OR/XOR, comparisons, adds, multiplies,
etc.  For now all of these @(see smallops) just take and return 64-bit
integers.  (We may some day want to implement operations of other sizes, but
keeping everything the same size seems like a good way to start, since it makes
guard proofs and type theorems very easy.)</p>

<p>We define the meaning of native expressions by way of a simple evaluator;
see @(see smalleval).  We can then write ACL2 functions that construct
expressions and use ACL2 to reason about the meaning of the expressions that
these functions produce.</p>

<h5>Compiling Small Expressions to LLVM</h5>

<p>For each primitive operation, there is a small, corresponding definition in
<a href='http://llvm.org/'>LLVM</a> assembly code.  Our intention is for these
LLVM definitions to exactly implement our ACL2 semantics.  Of course, we cannot
prove that this code is correct since LLVM is defined outside of ACL2.  But
these functions are small, we have been careful when writing them, and we at
least have a basic test suite that runs them against their ACL2
counterparts; see @(see llvm-smallops).</p>

<p>(LIES) Building on top of these LLVM definitions, we implement a compiler to
convert our expressions into corresponding LLVM assembly code fragments.  This
compiler is also unverified, but it is relatively simple.  The resulting
assembly code can be given to LLVM to compile into machine code, which gives us
a way to execute expressions ``on the metal'' without the overhead of an
interpreter.  It also makes it straightforward to evaluate these expressions
from languages like C.</p>

<h5>Big Integers, Operations, and Expressions</h5>

<p>We define a basic @(see bigint) representation and implement various
arithmetic operations on bigints as @(see bigops).  Using this representation,
we define another expression languagefor representing arbitrary-precision
bignum computations; see @(see bigexpr) and @(see bigeval).</p>

<p>(LIES) We implement (and prove correct) a compiler from bigexprs into
smallexprs.</p>

<h5>SV Connection</h5>

<p>(LIES) We implement (and prove correct) a translator from svexes into bigint
expressions.  We then hope to combine this translator with our compiler to LLVM
to obtain a very fast way to execute our hardware models and to integrate them
into external programs.</p>")

(xdoc::order-subtopics nativearith
                       (i64 smallops llvm-smallops smallexpr smalleval
                            bigint bigops bigexpr bigeval))

(local (xdoc::set-default-parents nativearith))




(defxdoc why-llvm
  :parents (llvm-operations)
  :short "Some comments about our choice of LLVM as a backend and comments
about other alternatives that we considered."

  :long "<p>Our expressions are simple enough that they could probably be
compiled into many other languages quite easily.  We have currently decided to
target the LLVM assembly language.  Below we discuss some of the thinking
behind this decision, and mention some of the alternatives that we
considered.</p>

<p>Our real goal is to provide a trustworthy expression language that we can
execute very efficiently and that we can incorporate into programs that are
written in other languages.  We especially want to be able to be compatible
with C, as it currently enjoys the special status of being the core language of
Unix systems and the lingua franca for the foreign function interfaces of most
high-level languages.</p>

<p>With these goals in mind, we felt fairly comfortable ruling out most
interpreted and scripting languages without much further consideration.  It
seems unlikely that we should target languages such as Java, C#, Ruby, Perl,
Python, etc., because perceive them to be relatively slow and because they
involve runtime systems that may complicate interfacing.</p>

<p>Our original thinking was that we would translate our expressions into C
programs.  We had some prior experience in doing something similar for the
@(see acl2::aig2c) tool (which converts and/inverter graphs into C/C++ code
fragments), and C seemed to be a fine choice for this purpose.  In particular,
we found that GCC and CLANG were able to handle the large code fragments that
we generated.  Targeting C instead of directly trying to write out assembly
language also resulted in a relatively portable tool and meant that we did not
have to write our own register allocator, worry about calling conventions,
etc.</p>

<p>But the aig2c tool was especially simple in that it was only meant to
implement single-bit expressions.  When we began looking into implementing more
interesting arithmetic operations in C, we were dismayed by the lack of
guarantees in areas such as overflow behavior, shifts by amounts larger than
the bit width, and (especially) coercions between signed/unsigned values.  We
would very much like to rely on 2's complement arithmetic with the correct
wraparound behavior.</p>

<p>When we started to look at LLVM we found that its semantics seem to be
better defined in these areas, and that it seemed to be not really any harder
to target than C would be&mdash;we can still have as many variables as we like,
and let it deal with issues like register allocation, calling conventions,
etc.</p>")

