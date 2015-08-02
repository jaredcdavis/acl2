// VL 2014 -- Verilog Toolkit, 2014 Edition
// Copyright (C) 2008-2015 Centaur Technology
//
// Contact:
//   Centaur Technology Formal Verification Group
//   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
//   http://www.centtech.com/
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
//   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
//   THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
//   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
//   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
//   DEALINGS IN THE SOFTWARE.
//
// Original author: Jared Davis <jared@centtech.com>

module dut;

  wire clk;
  wire [3:0] foo;
  wire [2:0] trunc1, trunc2, trunc3, trunc4, trunc5, trunc6, trunc7, trunc8;

  assign trunc1 = foo;
  assign trunc2 = (foo & 4'b0);

  always_comb
  begin
    trunc3 = foo;
    trunc4 = (foo & 4'b0);
  end

  always @(posedge clk)
  begin
    trunc5 <= foo;
    trunc6 <= (foo & 4'b0);
  end

  always_ff @(posedge clk)
  begin
    trunc7 <= foo;
    trunc8 <= (foo & 4'b0);
  end

  function [2:0] truncfun (logic [3:0] i) ;
    logic [2:0] trunc9;
    begin
      trunc9 = i;
      truncfun = i;
    end
  endfunction

  task trunctask (output [2:0] trunc10, input [3:0] i) ;
    logic [2:0] trunc11;
    begin
      trunc10 = i;
      trunc11 = i;
    end
  endtask

  logic [2:0] trunc12, trunc13;

  initial begin
    trunc12 = foo;
    trunc13 = (foo & 4'b0);
  end

  genvar i;
  wire [9:0][2:0] warr;
  generate
    for(i = 0;i < 10;++i) begin
      assign warr[i] = foo;
    end
  endgenerate

endmodule
