//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_request_slicer
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG      = '0,
  parameter int               STAGES          = 1,
  parameter bit               ASCENDING_ORDER = 1,
  parameter bit               FIFO_SLICER     = 1,
  parameter bit               DISABLE_MBFF    = 0
)(
  input var                 i_clk,
  input var                 i_rst_n,
  interface.request_slave   slave_if,
  interface.request_master  master_if
);
  localparam  int COMMAND_WIDTH     = get_packed_command_width(BUS_CONFIG);
  localparam  int WRITE_DATA_WIDTH  = get_packed_write_data_width(BUS_CONFIG, 1);
  localparam  int WRITE_DATA_STAGES = (BUS_CONFIG.profile != PZCOREBUS_CSR) ? STAGES : 0;

  logic [COMMAND_WIDTH-1:0]     slave_mcmd;
  logic [COMMAND_WIDTH-1:0]     master_mcmd;
  logic [WRITE_DATA_WIDTH-1:0]  slave_mdata;
  logic [WRITE_DATA_WIDTH-1:0]  master_mdata;

  always_comb begin
    slave_mcmd  = slave_if.get_packed_command();
    slave_mdata = slave_if.get_packed_write_data();
  end

  always_comb begin
    master_if.put_packed_command(master_mcmd);
    master_if.put_packed_write_data(master_mdata);
  end

  pzbcm_slicer #(
    .WIDTH            (COMMAND_WIDTH    ),
    .STAGES           (STAGES           ),
    .ASCENDING_ORDER  (ASCENDING_ORDER  ),
    .FULL_BANDWIDTH   (FIFO_SLICER      ),
    .DISABLE_MBFF     (DISABLE_MBFF     )
  ) u_command_slicer (
    .i_clk    (i_clk                  ),
    .i_rst_n  (i_rst_n                ),
    .i_valid  (slave_if.mcmd_valid    ),
    .o_ready  (slave_if.scmd_accept   ),
    .i_data   (slave_mcmd             ),
    .o_valid  (master_if.mcmd_valid   ),
    .i_ready  (master_if.scmd_accept  ),
    .o_data   (master_mcmd            )
  );

  pzbcm_slicer #(
    .WIDTH            (WRITE_DATA_WIDTH   ),
    .STAGES           (WRITE_DATA_STAGES  ),
    .ASCENDING_ORDER  (ASCENDING_ORDER    ),
    .FULL_BANDWIDTH   (FIFO_SLICER        ),
    .DISABLE_MBFF     (DISABLE_MBFF       )
  ) u_write_data_slicer (
    .i_clk    (i_clk                  ),
    .i_rst_n  (i_rst_n                ),
    .i_valid  (slave_if.mdata_valid   ),
    .o_ready  (slave_if.sdata_accept  ),
    .i_data   (slave_mdata            ),
    .o_valid  (master_if.mdata_valid  ),
    .i_ready  (master_if.sdata_accept ),
    .o_data   (master_mdata           )
  );
endmodule
