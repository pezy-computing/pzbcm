//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_response_async_fifo
  import  pzcorebus_pkg::*,
          pzbcm_async_fifo_pkg::calc_default_depth;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               STAGES            = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES,
  parameter int               RESPONSE_DEPTH    = calc_default_depth(STAGES),
  parameter bit               MERGE_RESET       = '0,
  parameter int               RESET_SYNC_STAGES = 2
)(
  input var                 i_slave_clk,
  input var                 i_slave_rst_n,
  interface.response_slave  slave_if,
  input var                 i_master_clk,
  input var                 i_master_rst_n,
  interface.response_master master_if
);
  localparam  int PACKED_RESPONSE_WIDTH = get_packed_response_width(BUS_CONFIG);

  logic                             empty;
  logic                             full;
  logic [PACKED_RESPONSE_WIDTH-1:0] slave_sresp;
  logic [PACKED_RESPONSE_WIDTH-1:0] master_sresp;

  always_comb begin
    slave_if.sresp_valid  = !empty;
    slave_if.put_packed_response(slave_sresp);
  end

  always_comb begin
    master_if.mresp_accept  = !full;
    master_sresp            = master_if.get_packed_response();
  end

  pzbcm_async_fifo #(
    .WIDTH              (PACKED_RESPONSE_WIDTH  ),
    .DEPTH              (RESPONSE_DEPTH         ),
    .STAGES             (STAGES                 ),
    .USE_OUT_DATA_RESET (1                      ),
    .MERGE_RESET        (MERGE_RESET            ),
    .RESET_SYNC_STAGES  (RESET_SYNC_STAGES      )
  ) u_async_fifo (
    .is_clk         (i_master_clk           ),
    .is_rst_n       (i_master_rst_n         ),
    .os_almost_full (),
    .os_full        (full                   ),
    .is_push        (master_if.sresp_valid  ),
    .is_data        (master_sresp           ),
    .id_clk         (i_slave_clk            ),
    .id_rst_n       (i_slave_rst_n          ),
    .od_empty       (empty                  ),
    .id_pop         (slave_if.mresp_accept  ),
    .od_data        (slave_sresp            )
  );
endmodule
