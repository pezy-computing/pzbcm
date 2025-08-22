//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzbcm_array_ff_slicer #(
  parameter int   WIDTH             = 1,
  parameter type  TYPE              = logic [WIDTH-1:0],
  parameter int   N                 = 1,
  parameter int   STAGES[N]         = '{default: 1},
  parameter int   ADDITONAL_STAGES  = 0,
  parameter bit   ASCENDING_ORDER   = 1,
  parameter bit   DISABLE_MBFF      = 0
)(
  input   var               i_clk,
  input   var               i_rst_n,
  input   var TYPE  [N-1:0] i_d,
  output  var TYPE  [N-1:0] o_q
);
  for (genvar i = 0;i < N;++i) begin : g
    pzbcm_ff_slicer #(
      .WIDTH            (WIDTH                        ),
      .TYPE             (TYPE                         ),
      .STAGES           (STAGES[i] + ADDITONAL_STAGES ),
      .ASCENDING_ORDER  (ASCENDING_ORDER              ),
      .DISABLE_MBFF     (DISABLE_MBFF                 )
    ) u_slicer (
      .i_clk    (i_clk    ),
      .i_rst_n  (i_rst_n  ),
      .i_d      (i_d[i]   ),
      .o_q      (o_q[i]   )
    );
  end
endmodule
