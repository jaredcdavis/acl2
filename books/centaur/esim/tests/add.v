/*

VL Regression Suite
Copyright (C) David L. Rager

License: (An MIT/X11-style license)

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the "Software"),
to deal in the Software without restriction, including without limitation
the rights to use, copy, modify, merge, publish, distribute, sublicense,
and/or sell copies of the Software, and to permit persons to whom the
Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
DEALINGS IN THE SOFTWARE.

Original author: David Rager <ragerdl@defthm.com>

Other entities should feel free to add to the "VL Regression Suite"
with files that have different licenses and/or copyrights.

*/


// add.v
//
// These are simple adders.

module add1 (
  output [0:0] out,
  input [0:0] abus,
  input [0:0] bbus
);
assign out = abus + bbus;
endmodule

module add2 (
  output [1:0] out,
  input [1:0] abus,
  input [1:0] bbus
);
assign out = abus + bbus;
endmodule

module add3 (
  output [2:0] out,
  input [2:0] abus,
  input [2:0] bbus
);
assign out = abus + bbus;
endmodule

module add4 (
  output [3:0] out,
  input [3:0] abus,
  input [3:0] bbus
);
assign out = abus + bbus;
endmodule

module add8 (
  output [7:0] out,
  input [7:0] abus,
  input [7:0] bbus
);
assign out = abus + bbus;
endmodule

module add16 (
  output [15:0] out,
  input [15:0] abus,
  input [15:0] bbus
);
assign out = abus + bbus;
endmodule

module add32 (
  output [31:0] out,
  input [31:0] abus,
  input [31:0] bbus
);
assign out = abus + bbus;
endmodule

module add64 (
  output [63:0] out,
  input [63:0] abus,
  input [63:0] bbus
);
assign out = abus + bbus;
endmodule

module add128 (
  output [127:0] out,
  input [127:0] abus,
  input [127:0] bbus
);
assign out = abus + bbus;
endmodule

module add256 (
  output [255:0] out,
  input [255:0] abus,
  input [255:0] bbus
);
assign out = abus + bbus;
endmodule

module add512 (
  output [511:0] out,
  input [511:0] abus,
  input [511:0] bbus
);
assign out = abus + bbus;
endmodule

module add1024 (
  output [1023:0] out,
  input [1023:0] abus,
  input [1023:0] bbus
);
assign out = abus + bbus;
endmodule

