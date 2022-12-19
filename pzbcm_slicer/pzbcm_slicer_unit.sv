//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzbcm_slicer_unit #(
  parameter int WIDTH           = 1,
  parameter bit FULL_BANDWIDTH  = 1,
  parameter bit DISABLE_MBFF    = 0
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_valid,
  output  var             o_ready,
  input   var [WIDTH-1:0] i_data,
  output  var             o_valid,
  input   var             i_ready,
  output  var [WIDTH-1:0] o_data
);
  if (FULL_BANDWIDTH) begin : g
    pzbcm_slicer_unit_full_bandwidth #(
      .WIDTH        (WIDTH        ),
      .DISABLE_MBFF (DISABLE_MBFF )
    ) u_slicer_unit (
      .i_clk    (i_clk    ),
      .i_rst_n  (i_rst_n  ),
      .i_valid  (i_valid  ),
      .o_ready  (o_ready  ),
      .i_data   (i_data   ),
      .o_valid  (o_valid  ),
      .i_ready  (i_ready  ),
      .o_data   (o_data   )
    );
  end
  else begin : g
    pzbcm_slicer_unit_half_bandwidth #(
      .WIDTH        (WIDTH        ),
      .DISABLE_MBFF (DISABLE_MBFF )
    ) u_slicer_unit (
      .i_clk    (i_clk    ),
      .i_rst_n  (i_rst_n  ),
      .i_valid  (i_valid  ),
      .o_ready  (o_ready  ),
      .i_data   (i_data   ),
      .o_valid  (o_valid  ),
      .i_ready  (i_ready  ),
      .o_data   (o_data   )
    );
  end
endmodule
