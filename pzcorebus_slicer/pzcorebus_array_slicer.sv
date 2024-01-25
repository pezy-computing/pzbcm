//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_array_slicer
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               N                 = 1,
  parameter int               STAGES[N]         = '{default: 0},
  parameter int               ADDITONAL_STAGES  = 0,
  parameter bit               ASCENDING_ORDER   = 1,
  parameter bit               FIFO_SLICER       = 1,
  parameter bit               DISABLE_MBFF      = 0,
  parameter bit               USE_RESET         = 1,
  parameter bit               REQUEST_VALID     = 1,
  parameter bit               RESPONSE_VALID    = 1
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if[N],
  pzcorebus_if.master master_if[N]
);
  for (genvar i = 0;i < N;++i) begin : g
    pzcorebus_slicer #(
      .BUS_CONFIG       (BUS_CONFIG                   ),
      .STAGES           (STAGES[i] + ADDITONAL_STAGES ),
      .ASCENDING_ORDER  (ASCENDING_ORDER              ),
      .FIFO_SLICER      (FIFO_SLICER                  ),
      .DISABLE_MBFF     (DISABLE_MBFF                 ),
      .USE_RESET        (USE_RESET                    ),
      .REQUEST_VALID    (REQUEST_VALID                ),
      .RESPONSE_VALID   (RESPONSE_VALID               )
    ) u_slicer (
      .i_clk      (i_clk        ),
      .i_rst_n    (i_rst_n      ),
      .slave_if   (slave_if[i]  ),
      .master_if  (master_if[i] )
    );
  end
endmodule
