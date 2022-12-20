//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_edge_detector #(
  parameter int             WIDTH         = 1,
  parameter bit [WIDTH-1:0] INITIAL_VALUE = '0
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_clear,
  input   var [WIDTH-1:0] i_d,
  output  var [WIDTH-1:0] o_edge,
  output  var [WIDTH-1:0] o_posedge,
  output  var [WIDTH-1:0] o_negedge
);
  logic [WIDTH-1:0] d;

  assign  o_edge    = ( i_d) ^ ( d) & (~i_clear);
  assign  o_posedge = ( i_d) & (~d) & (~i_clear);
  assign  o_negedge = (~i_d) & ( d) & (~i_clear);

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      d <= INITIAL_VALUE;
    end
    else if (i_clear) begin
      d <= INITIAL_VALUE;
    end
    else begin
      d <= i_d;
    end
  end
endmodule
