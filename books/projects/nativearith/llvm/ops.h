// Native Arithmetic Library
// Copyright (C) 2015-2016 Kookamara LLC
//
// Contact:
//
//   Kookamara LLC
//   11410 Windermere Meadows
//   Austin, TX 78759, USA
//   http://www.kookamara.com/
//
// License: (An MIT/X11-style license)
//
//   Permission is hereby granted, free of charge, to any person obtaining a
//   copy of this software and associated documentation files (the "Software"),
//   to deal in the Software without restriction, including without limitation
//   the rights to use, copy, modify, merge, publish, distribute, sublicense,
//   and/or sell copies of the Software, and to permit persons to whom the
//   Software is furnished to do so, subject to the following conditions:
//
//   The above copyright notice and this permission notice shall be included in
//   all copies or substantial portions of the Software.
//
//   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
//   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
//   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@kookamara.com>

#ifndef NARITH_OPS_H
#define NARITH_OPS_H

#include <stdint.h>

extern int64_t narith_i64eql(int64_t a, int64_t b);
extern int64_t narith_i64neq(int64_t a, int64_t b);
extern int64_t narith_i64sle(int64_t a, int64_t b);
extern int64_t narith_i64slt(int64_t a, int64_t b);
extern int64_t narith_i64sge(int64_t a, int64_t b);
extern int64_t narith_i64sgt(int64_t a, int64_t b);
extern int64_t narith_i64bitand(int64_t a, int64_t b);
extern int64_t narith_i64bitor(int64_t a, int64_t b);
extern int64_t narith_i64bitxor(int64_t a, int64_t b);
extern int64_t narith_i64plus(int64_t a, int64_t b);
extern int64_t narith_i64minus(int64_t a, int64_t b);
extern int64_t narith_i64times(int64_t a, int64_t b);
extern int64_t narith_i64sdiv(int64_t a, int64_t b);

#endif
