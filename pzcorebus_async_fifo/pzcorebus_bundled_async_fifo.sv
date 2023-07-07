//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_bundled_async_fifo
  import  pzcorebus_pkg::*,
          pzbcm_async_fifo_pkg::calc_default_depth;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               REQUEST_CHANNELS  = 1,
  parameter int               RESPONSE_CHANNELS = 1,
  parameter int               STAGES            = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES,
  parameter int               COMMAND_DEPTH     = calc_default_depth(STAGES),
  parameter int               DATA_DEPTH        = calc_default_depth(STAGES),
  parameter int               RESPONSE_DEPTH    = calc_default_depth(STAGES),
  parameter bit               MERGE_RESET       = '0,
  parameter int               RESET_SYNC_STAGES = 2
)(
  input var                   i_slave_clk,
  input var                   i_slave_rst_n,
  pzcorebus_bundled_if.slave  slave_if,
  input var                   i_master_clk,
  input var                   i_master_rst_n,
  pzcorebus_bundled_if.master master_if
);
  initial begin
    assume (slave_if.REQUEST_CHANNELS   == REQUEST_CHANNELS);
    assume (slave_if.RESPONSE_CHANNELS  == RESPONSE_CHANNELS);
    assume (master_if.REQUEST_CHANNELS  == REQUEST_CHANNELS);
    assume (master_if.RESPONSE_CHANNELS == RESPONSE_CHANNELS);
  end

  localparam  int PACKED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG);
  localparam  int PAKCED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1);
  localparam  int PACKED_RESPONSE_WIDTH   = get_packed_response_width(BUS_CONFIG);

  logic slave_rst_n;
  logic master_rst_n;

  pzbcm_async_fifo_reset_sync #(
    .MERGE_RESET        (MERGE_RESET        ),
    .RESET_SYNC_STAGES  (RESET_SYNC_STAGES  )
  ) u_reset_sync (
    .is_clk   (i_slave_clk    ),
    .is_rst_n (i_slave_rst_n  ),
    .os_rst_n (slave_rst_n    ),
    .id_clk   (i_master_clk   ),
    .id_rst_n (i_master_rst_n ),
    .od_rst_n (master_rst_n   )
  );

  for (genvar i = 0;i < REQUEST_CHANNELS;++i) begin : g_request
    logic [1:0] empty;
    logic [1:0] full;

    always_comb begin
      slave_if.scmd_accept[i]   = !full[0];
      slave_if.sdata_accept[i]  = !full[1];
    end

    always_comb begin
      master_if.mcmd_valid[i]   = !empty[0];
      master_if.mdata_valid[i]  = !empty[1];
    end

    pzbcm_async_fifo #(
      .WIDTH              (PACKED_COMMAND_WIDTH ),
      .DEPTH              (COMMAND_DEPTH        ),
      .STAGES             (STAGES               ),
      .USE_OUT_DATA_RESET (1                    )
    ) u_command_async_fifo (
      .is_clk         (i_slave_clk              ),
      .is_rst_n       (slave_rst_n              ),
      .os_almost_full (),
      .os_full        (full[0]                  ),
      .is_push        (slave_if.mcmd_valid[i]   ),
      .is_data        (slave_if.mcmd[i]         ),
      .id_clk         (i_master_clk             ),
      .id_rst_n       (master_rst_n             ),
      .od_empty       (empty[0]                 ),
      .id_pop         (master_if.scmd_accept[i] ),
      .od_data        (master_if.mcmd[i]        )
    );

    pzbcm_async_fifo #(
      .WIDTH  (PAKCED_WRITE_DATA_WIDTH  ),
      .DEPTH  (DATA_DEPTH               ),
      .STAGES (STAGES                   )
    ) u_async_fifo (
      .is_clk         (i_slave_clk                ),
      .is_rst_n       (slave_rst_n                ),
      .os_almost_full (),
      .os_full        (full[1]                    ),
      .is_push        (slave_if.mdata_valid[i]    ),
      .is_data        (slave_if.mdata[i]          ),
      .id_clk         (i_master_clk               ),
      .id_rst_n       (master_rst_n               ),
      .od_empty       (empty[1]                   ),
      .id_pop         (master_if.sdata_accept[i]  ),
      .od_data        (master_if.mdata[i]         )
    );
  end

  for (genvar i = 0;i < RESPONSE_CHANNELS;++i) begin : g_response
    logic empty;
    logic full;

    always_comb begin
      master_if.mresp_accept[i] = !full;
    end

    always_comb begin
      slave_if.sresp_valid[i] = !empty;
    end

    pzbcm_async_fifo #(
      .WIDTH              (PACKED_RESPONSE_WIDTH  ),
      .DEPTH              (RESPONSE_DEPTH         ),
      .STAGES             (STAGES                 ),
      .USE_OUT_DATA_RESET (1                      )
    ) u_async_fifo (
      .is_clk         (i_master_clk             ),
      .is_rst_n       (master_rst_n             ),
      .os_almost_full (),
      .os_full        (full                     ),
      .is_push        (master_if.sresp_valid[i] ),
      .is_data        (master_if.sresp[i]       ),
      .id_clk         (i_slave_clk              ),
      .id_rst_n       (slave_rst_n              ),
      .od_empty       (empty                    ),
      .id_pop         (slave_if.mresp_accept[i] ),
      .od_data        (slave_if.sresp[i]        )
    );
  end
endmodule
