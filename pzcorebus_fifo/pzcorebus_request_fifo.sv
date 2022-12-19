//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_request_fifo
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               COMMAND_DEPTH     = 2,
  parameter int               COMMAND_THRESHOLD = COMMAND_DEPTH,
  parameter bit               COMMAND_VALID     = 1,
  parameter int               DATA_DEPTH        = 2,
  parameter int               DATA_THRESHOLD    = DATA_DEPTH,
  parameter bit               DATA_VALID        = 1,
  parameter bit               FLAG_FF_OUT       = 1,
  parameter bit               DATA_FF_OUT       = 1
)(
  input   var               i_clk,
  input   var               i_rst_n,
  input   var               i_clear,
  output  var [1:0]         o_empty,
  output  var [1:0]         o_almost_full,
  output  var [1:0]         o_full,
  interface.request_slave   slave_if,
  interface.request_master  master_if
);
  localparam  int PACKED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG);
  localparam  int PAKCED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1);
  localparam  int PACKED_RESPONSE_WIDTH   = get_packed_response_width(BUS_CONFIG);

  typedef logic [PACKED_COMMAND_WIDTH-1:0]    pzcorebus_packed_command;
  typedef logic [PAKCED_WRITE_DATA_WIDTH-1:0] pzcorebus_packed_write_data;
  typedef logic [PACKED_RESPONSE_WIDTH-1:0]   pzcorebus_packed_response;

  logic [1:0]                 empty;
  logic [1:0]                 almost_full;
  logic [1:0]                 full;
  logic                       scmd_accept;
  pzcorebus_packed_command    slave_mcmd;
  logic                       mcmd_valid;
  pzcorebus_packed_command    master_mcmd;
  logic                       sdata_accept;
  pzcorebus_packed_write_data slave_mdata;
  logic                       mdata_valid;
  pzcorebus_packed_write_data master_mdata;
  logic                       sresp_valid;
  pzcorebus_packed_response   slave_sresp;
  logic                       mresp_accept;
  pzcorebus_packed_response   master_sresp;

  always_comb begin
    o_empty       = empty;
    o_almost_full = almost_full;
    o_full        = full;
  end

  always_comb begin
    slave_if.scmd_accept  = scmd_accept;
    slave_mcmd            = slave_if.get_packed_command();
    slave_if.sdata_accept = sdata_accept;
    slave_mdata           = slave_if.get_packed_write_data();
  end

  always_comb begin
    master_if.mcmd_valid  = mcmd_valid;
    master_if.put_packed_command(master_mcmd);
    master_if.mdata_valid = mdata_valid;
    master_if.put_packed_write_data(master_mdata);
  end

  if (COMMAND_VALID && (COMMAND_DEPTH >= 1)) begin : g_command
    pzbcm_fifo #(
      .WIDTH        (PACKED_COMMAND_WIDTH ),
      .DEPTH        (COMMAND_DEPTH        ),
      .THRESHOLD    (COMMAND_THRESHOLD    ),
      .FLAG_FF_OUT  (FLAG_FF_OUT          ),
      .DATA_FF_OUT  (DATA_FF_OUT          )
    ) u_fifo (
      .i_clk          (i_clk                  ),
      .i_rst_n        (i_rst_n                ),
      .i_clear        (i_clear                ),
      .o_empty        (empty[0]               ),
      .o_almost_full  (almost_full[0]         ),
      .o_full         (full[0]                ),
      .o_word_count   (),
      .i_push         (slave_if.mcmd_valid    ),
      .i_data         (slave_mcmd             ),
      .i_pop          (master_if.scmd_accept  ),
      .o_data         (master_mcmd            )
    );

    always_comb begin
      scmd_accept = !full[0];
      mcmd_valid  = !empty[0];
    end
  end
  else begin : g_command
    always_comb begin
      empty[0]        = '1;
      almost_full[0]  = '0;
      full[0]         = '0;
    end

    always_comb begin
      scmd_accept = master_if.scmd_accept;
      mcmd_valid  = slave_if.mcmd_valid;
      master_mcmd = slave_mcmd;
    end
  end

  if (DATA_VALID && (DATA_DEPTH >= 1) && (BUS_CONFIG.profile != PZCOREBUS_CSR)) begin : g_data
    pzbcm_fifo #(
      .WIDTH        (PAKCED_WRITE_DATA_WIDTH  ),
      .DEPTH        (DATA_DEPTH               ),
      .THRESHOLD    (DATA_THRESHOLD           ),
      .FLAG_FF_OUT  (FLAG_FF_OUT              ),
      .DATA_FF_OUT  (DATA_FF_OUT              )
    ) u_fifo (
      .i_clk          (i_clk                  ),
      .i_rst_n        (i_rst_n                ),
      .i_clear        (i_clear                ),
      .o_empty        (empty[1]               ),
      .o_almost_full  (almost_full[1]         ),
      .o_full         (full[1]                ),
      .o_word_count   (),
      .i_push         (slave_if.mdata_valid   ),
      .i_data         (slave_mdata            ),
      .i_pop          (master_if.sdata_accept ),
      .o_data         (master_mdata           )
    );

    always_comb begin
      sdata_accept  = !full[1];
      mdata_valid   = !empty[1];
    end
  end
  else begin : g_data
    always_comb begin
      empty[1]        = '1;
      almost_full[1]  = '0;
      full[1]         = '0;
    end

    always_comb begin
      sdata_accept  = master_if.sdata_accept;
      mdata_valid   = slave_if.mdata_valid;
      master_mdata  = slave_mdata;
    end
  end
endmodule
