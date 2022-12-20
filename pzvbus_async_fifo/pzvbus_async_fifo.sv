//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzvbus_async_fifo #(
  parameter int DEPTH   = 4,
  parameter int STAGES  = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES
)(
  input var         i_slave_clk,
  input var         i_slave_rst_n,
  input var         i_slave_push,
  pzvbus_if.slave   slave_if,
  input var         i_master_clk,
  input var         i_master_rst_n,
  input var         i_master_pop,
  pzvbus_if.master  master_if
);
  typedef slave_if.__payload_with_valid __payload_with_valid;

  logic                 empty;
  __payload_with_valid  in;
  __payload_with_valid  out;

  assign  in.valid          = slave_if.valid;
  assign  in.payload        = slave_if.payload;
  assign  master_if.valid   = (!empty) ? out.valid : '0;
  assign  master_if.payload = out.payload;

  pzbcm_async_fifo #(
    .TYPE   (__payload_with_valid ),
    .DEPTH  (DEPTH                ),
    .STAGES (STAGES               )
  ) u_async_fifo (
    .is_clk         (i_slave_clk    ),
    .is_rst_n       (i_slave_rst_n  ),
    .os_almost_full (),
    .os_full        (),
    .is_push        (i_slave_push   ),
    .is_data        (in             ),
    .id_clk         (i_master_clk   ),
    .id_rst_n       (i_master_rst_n ),
    .od_empty       (empty          ),
    .id_pop         (i_master_pop   ),
    .od_data        (out            )
  );
endmodule
