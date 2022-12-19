//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzbcm_delay #(
  parameter int   DELAY         = 1,
  parameter int   WIDTH         = 1,
  parameter type  TYPE          = logic[WIDTH-1:0],
  parameter TYPE  INITIAL_VALUE = TYPE'(0)
)(
  input   var       i_clk,
  input   var       i_rst_n,
  input   var TYPE  i_d,
  output  var TYPE  o_d
);
  if (DELAY >= 1) begin : g_delay
    TYPE  delay[DELAY];

    assign  o_d = delay[DELAY-1];
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        delay <= '{default: INITIAL_VALUE};
      end
      else begin
        delay[0]  <= i_d;
        for (int i = 1;i < DELAY;++i) begin
          delay[i]  <= delay[i-1];
        end
      end
    end
  end
  else begin : g_no_delay
    assign  o_d = i_d;
  end
endmodule
