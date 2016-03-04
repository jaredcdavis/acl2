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

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>

extern int64_t demo_circuit(int64_t *in, int64_t* out);

int main()
{
    printf("Native Arithmetic Library Demo\n");

    int64_t in[30] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                       10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
                       20, 21, 22, 23, 24, 25, 26, 27, 28, 29 };
    int64_t out[15];

    printf("Inputs:\n");
    for(int i = 0; i < 30; ++i) {
        printf(" - in[%d] = %" PRId64 "\n", i, in[i]);
    }

    int64_t res = demo_circuit(in, out);

    printf("Res is %" PRId64 "\n", res);

    printf("Outputs:\n");
    for(int i = 0; i < 15; ++i) {
        printf(" - out[%d] = %" PRId64 "\n", i, out[i]);
    }

    return 0;
}
