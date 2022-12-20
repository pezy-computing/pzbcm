//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzhsbus_async_fifo #(
  parameter int DEPTH   = 4,
  parameter int STAGES  = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES
)(
  input var         i_slave_clk,
  input var         i_slave_rst_n,
  pzhsbus_if.slave  slave_if,
  input var         i_master_clk,
  input var         i_master_rst_n,
  pzhsbus_if.master master_if
);
  typedef slave_if.__payload  __payload;

  logic full;
  logic empty;

  assign  slave_if.ready  = ~full;
  assign  master_if.valid = ~empty;

  pzbcm_async_fifo #(
    .TYPE   (__payload  ),
    .DEPTH  (DEPTH      ),
    .STAGES (STAGES     )
  ) u_async_fifo (
    .is_clk         (i_slave_clk        ),
    .is_rst_n       (i_slave_rst_n      ),
    .os_almost_full (),
    .os_full        (full               ),
    .is_push        (slave_if.valid     ),
    .is_data        (slave_if.payload   ),
    .id_clk         (i_master_clk       ),
    .id_rst_n       (i_master_rst_n     ),
    .od_empty       (empty              ),
    .id_pop         (master_if.ready    ),
    .od_data        (master_if.payload  )
  );
endmodule
