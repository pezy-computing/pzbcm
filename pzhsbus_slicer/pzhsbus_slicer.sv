//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzhsbus_slicer #(
  parameter type  PAYLOAD         = logic,
  parameter int   STAGES          = 1,
  parameter bit   ASCENDING_ORDER = 1,
  parameter bit   USE_FIFO        = 1,
  parameter bit   DISABLE_MBFF    = 0
)(
  input var         i_clk,
  input var         i_rst_n,
  pzhsbus_if.slave  slave_if,
  pzhsbus_if.master master_if
);
  pzbcm_slicer #(
    .WIDTH            ($bits(PAYLOAD)   ),
    .TYPE             (PAYLOAD          ),
    .STAGES           (STAGES           ),
    .ASCENDING_ORDER  (ASCENDING_ORDER  ),
    .FULL_BANDWIDTH   (USE_FIFO         ),
    .DISABLE_MBFF     (DISABLE_MBFF     )
  ) u_slicer (
    .i_clk    (i_clk              ),
    .i_rst_n  (i_rst_n            ),
    .i_valid  (slave_if.valid     ),
    .o_ready  (slave_if.ready     ),
    .i_data   (slave_if.payload   ),
    .o_valid  (master_if.valid    ),
    .i_ready  (master_if.ready    ),
    .o_data   (master_if.payload  )
  );
endmodule
