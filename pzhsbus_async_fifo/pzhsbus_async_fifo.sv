//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzhsbus_async_fifo
  import  pzbcm_async_fifo_pkg::calc_default_depth;
#(
  parameter int STAGES            = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES,
  parameter int DEPTH             = calc_default_depth(STAGES),
  parameter bit MERGE_RESET       = '0,
  parameter int RESET_SYNC_STAGES = 2
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
    .TYPE               (__payload            ),
    .DEPTH              (DEPTH                ),
    .STAGES             (STAGES               ),
    .MERGE_RESET        (MERGE_RESET          ),
    .RESET_SYNC_STAGES  (RESET_SYNC_STAGES    )
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
