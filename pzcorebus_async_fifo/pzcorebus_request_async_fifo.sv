//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_request_async_fifo
  import  pzcorebus_pkg::*,
          pzbcm_async_fifo_pkg::calc_default_depth;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               STAGES            = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES,
  parameter int               COMMAND_DEPTH     = calc_default_depth(STAGES),
  parameter int               DATA_DEPTH        = calc_default_depth(STAGES),
  parameter bit               MERGE_RESET       = '0,
  parameter int               RESET_SYNC_STAGES = 2,
  parameter bit               SVA_CHECKER       = 1
)(
  input var                 i_slave_clk,
  input var                 i_slave_rst_n,
  interface.request_slave   slave_if,
  input var                 i_master_clk,
  input var                 i_master_rst_n,
  interface.request_master  master_if
);
  localparam  int PACKED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG);
  localparam  int PAKCED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1);

  typedef logic [PACKED_COMMAND_WIDTH-1:0]    pzcorebus_packed_command;
  typedef logic [PAKCED_WRITE_DATA_WIDTH-1:0] pzcorebus_packed_write_data;

  logic [1:0]                 empty;
  logic [1:0]                 full;
  logic                       slave_rst_n;
  logic                       master_rst_n;
  pzcorebus_packed_command    slave_mcmd;
  pzcorebus_packed_command    master_mcmd;
  pzcorebus_packed_write_data slave_mdata;
  pzcorebus_packed_write_data master_mdata;

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

  always_comb begin
    slave_if.scmd_accept    = !full[0];
    slave_mcmd              = slave_if.get_packed_command();
    slave_if.sdata_accept   = !full[1];
    slave_mdata             = slave_if.get_packed_write_data();
  end

  always_comb begin
    master_if.mcmd_valid  = !empty[0];
    master_if.put_packed_command(master_mcmd);
    master_if.mdata_valid = !empty[1];
    master_if.put_packed_write_data(master_mdata);
  end

  if (1) begin : g_command
    pzbcm_async_fifo #(
      .WIDTH              (PACKED_COMMAND_WIDTH ),
      .DEPTH              (COMMAND_DEPTH        ),
      .STAGES             (STAGES               ),
      .USE_OUT_DATA_RESET (1                    )
    ) u_async_fifo (
      .is_clk         (i_slave_clk            ),
      .is_rst_n       (slave_rst_n            ),
      .os_almost_full (),
      .os_full        (full[0]                ),
      .is_push        (slave_if.mcmd_valid    ),
      .is_data        (slave_mcmd             ),
      .id_clk         (i_master_clk           ),
      .id_rst_n       (master_rst_n           ),
      .od_empty       (empty[0]               ),
      .id_pop         (master_if.scmd_accept  ),
      .od_data        (master_mcmd            )
    );
  end

  if (is_memory_profile(BUS_CONFIG)) begin : g_data
    pzbcm_async_fifo #(
      .WIDTH  (PAKCED_WRITE_DATA_WIDTH  ),
      .DEPTH  (DATA_DEPTH               ),
      .STAGES (STAGES                   )
    ) u_async_fifo (
      .is_clk         (i_slave_clk            ),
      .is_rst_n       (slave_rst_n            ),
      .os_almost_full (),
      .os_full        (full[1]                ),
      .is_push        (slave_if.mdata_valid   ),
      .is_data        (slave_mdata            ),
      .id_clk         (i_master_clk           ),
      .id_rst_n       (master_rst_n           ),
      .od_empty       (empty[1]               ),
      .id_pop         (master_if.sdata_accept ),
      .od_data        (master_mdata           )
    );
  end
  else begin : g_data
    always_comb begin
      full[1] = '0;
    end

    always_comb begin
      empty[1]      = '1;
      master_mdata  = '0;
    end
  end

//--------------------------------------------------------------
//  SVA checker
//--------------------------------------------------------------
  if (PZCOREBUS_ENABLE_SVA_CHECKER) begin : g_sva
    pzcorebus_request_sva_checker #(
      .BUS_CONFIG   (BUS_CONFIG   ),
      .SVA_CHECKER  (SVA_CHECKER  )
    ) u_sva_checker (
      .i_clk    (i_slave_clk    ),
      .i_rst_n  (i_slave_rst_n  ),
      .bus_if   (slave_if       )
    );
  end
endmodule
