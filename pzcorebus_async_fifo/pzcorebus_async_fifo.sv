//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_async_fifo
  import  pzcorebus_pkg::*,
          pzbcm_async_fifo_pkg::calc_default_depth;
#(
  parameter pzcorebus_config  BUS_CONFIG            = '0,
  parameter int               STAGES                = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES,
  parameter int               COMMAND_DEPTH         = calc_default_depth(STAGES),
  parameter int               DATA_DEPTH            = calc_default_depth(STAGES),
  parameter int               RESPONSE_DEPTH        = calc_default_depth(STAGES),
  parameter bit               MERGE_RESET           = '0,
  parameter int               RESET_SYNC_STAGES     = 2,
  parameter bit               SVA_CHECKER           = 1,
  parameter bit               REQUEST_SVA_CHECKER   = SVA_CHECKER,
  parameter bit               RESPONSE_SVA_CHECKER  = SVA_CHECKER
)(
  input var           i_slave_clk,
  input var           i_slave_rst_n,
  pzcorebus_if.slave  slave_if,
  input var           i_master_clk,
  input var           i_master_rst_n,
  pzcorebus_if.master master_if
);
  localparam  int PACKED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG);
  localparam  int PAKCED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1);
  localparam  int PACKED_RESPONSE_WIDTH   = get_packed_response_width(BUS_CONFIG);

  typedef logic [PACKED_COMMAND_WIDTH-1:0]    pzcorebus_packed_command;
  typedef logic [PAKCED_WRITE_DATA_WIDTH-1:0] pzcorebus_packed_write_data;
  typedef logic [PACKED_RESPONSE_WIDTH-1:0]   pzcorebus_packed_response;

  logic [2:0]                 empty;
  logic [2:0]                 full;
  logic                       slave_rst_n;
  logic                       master_rst_n;
  pzcorebus_packed_command    slave_mcmd;
  pzcorebus_packed_command    master_mcmd;
  pzcorebus_packed_write_data slave_mdata;
  pzcorebus_packed_write_data master_mdata;
  pzcorebus_packed_response   slave_sresp;
  pzcorebus_packed_response   master_sresp;

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
    slave_if.sresp_valid  = !empty[2];
    slave_if.put_packed_response(slave_sresp);
  end

  always_comb begin
    master_if.mcmd_valid  = !empty[0];
    master_if.put_packed_command(master_mcmd);
    master_if.mdata_valid = !empty[1];
    master_if.put_packed_write_data(master_mdata);
  end

  always_comb begin
    master_if.mresp_accept  = !full[2];
    master_sresp            = master_if.get_packed_response();
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

  if (1) begin : g_response
    pzbcm_async_fifo #(
      .WIDTH              (PACKED_RESPONSE_WIDTH  ),
      .DEPTH              (RESPONSE_DEPTH         ),
      .STAGES             (STAGES                 ),
      .USE_OUT_DATA_RESET (1                      )
    ) u_async_fifo (
      .is_clk         (i_master_clk           ),
      .is_rst_n       (master_rst_n           ),
      .os_almost_full (),
      .os_full        (full[2]                ),
      .is_push        (master_if.sresp_valid  ),
      .is_data        (master_sresp           ),
      .id_clk         (i_slave_clk            ),
      .id_rst_n       (slave_rst_n            ),
      .od_empty       (empty[2]               ),
      .id_pop         (slave_if.mresp_accept  ),
      .od_data        (slave_sresp            )
    );
  end

//--------------------------------------------------------------
//  SVA checker
//--------------------------------------------------------------
  if (PZCOREBUS_ENABLE_SVA_CHECKER) begin : g_sva
    pzcorebus_sva_checker #(
      .BUS_CONFIG           (BUS_CONFIG           ),
      .REQUEST_SVA_CHECKER  (REQUEST_SVA_CHECKER  ),
      .RESPONSE_SVA_CHECKER (RESPONSE_SVA_CHECKER )
    ) u_sva_checker (
      .i_request_clk    (i_slave_clk    ),
      .i_request_rst_n  (i_slave_rst_n  ),
      .request_bus_if   (slave_if       ),
      .i_response_clk   (i_master_clk   ),
      .i_response_rst_n (i_master_rst_n ),
      .response_bus_if  (master_if      )
    );
  end
endmodule
