//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_packer
  import  pzcorebus_pkg::*,
          pzbcm_sram_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG            = '0,
  parameter int               COMMAND_DEPTH         = 1,
  parameter int               DATA_DEPTH            = BUS_CONFIG.max_burst_length,
  parameter bit [1:0]         SLAVE_SLICER          = '0,
  parameter bit [1:0]         MASTER_SLICER         = '0,
  parameter pzbcm_sram_params SRAM_PARAMS           = '0,
  parameter type              SRAM_CONFIG           = logic,
  parameter bit               SVA_CHECKER           = '1,
  parameter bit               REQUEST_SVA_CHECKER   = SVA_CHECKER,
  parameter bit               RESPONSE_SVA_CHECKER  = SVA_CHECKER
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_clear,
  output  var [1:0]       o_fifo_empty,
  output  var [1:0]       o_fifo_full,
  input   var SRAM_CONFIG i_sram_config,
  pzcorebus_if.slave      slave_if,
  pzcorebus_if.master     master_if
);
  pzcorebus_if #(BUS_CONFIG)          slicer_if[2]();
  pzcorebus_request_if #(BUS_CONFIG)  request_if();

  pzcorebus_slicer #(
    .BUS_CONFIG           (BUS_CONFIG           ),
    .REQUEST_VALID        (SLAVE_SLICER[0]      ),
    .RESPONSE_VALID       (SLAVE_SLICER[1]      ),
    .REQUEST_SVA_CHECKER  (REQUEST_SVA_CHECKER  ),
    .RESPONSE_SVA_CHECKER (0                    )
  ) u_slave_slicer (
    .i_clk      (i_clk        ),
    .i_rst_n    (i_rst_n      ),
    .slave_if   (slave_if     ),
    .master_if  (slicer_if[0] )
  );

//--------------------------------------------------------------
//  Command FIFO
//--------------------------------------------------------------
  pzcorebus_command_fifo #(
    .BUS_CONFIG (BUS_CONFIG     ),
    .DEPTH      (COMMAND_DEPTH  )
  ) u_command_fifo (
    .i_clk          (i_clk            ),
    .i_rst_n        (i_rst_n          ),
    .i_clear        (i_clear          ),
    .o_empty        (o_fifo_empty[0]  ),
    .o_almost_full  (),
    .o_full         (o_fifo_full[0]   ),
    .slave_if       (slicer_if[0]     ),
    .master_if      (request_if       )
  );

//--------------------------------------------------------------
//  Write Data FIFO
//--------------------------------------------------------------
  if (SRAM_PARAMS != '0) begin : g_data_fifo
    pzcorebus_packer_data_fifo #(
      .BUS_CONFIG   (BUS_CONFIG   ),
      .SRAM_PARAMS  (SRAM_PARAMS  ),
      .SRAM_CONFIG  (SRAM_CONFIG  )
    ) u_data_fifo (
      .i_clk          (i_clk            ),
      .i_rst_n        (i_rst_n          ),
      .i_clear        (i_clear          ),
      .o_fifo_empty   (o_fifo_empty[1]  ),
      .o_fifo_full    (o_fifo_full[1]   ),
      .i_sram_config  (i_sram_config    ),
      .slave_if       (slicer_if[0]     ),
      .master_if      (request_if       )
    );
  end
  else begin : g_write_data_fifo
    pzcorebus_write_data_fifo #(
      .BUS_CONFIG (BUS_CONFIG ),
      .DEPTH      (DATA_DEPTH )
    ) u_data_fifo (
      .i_clk          (i_clk            ),
      .i_rst_n        (i_rst_n          ),
      .i_clear        (i_clear          ),
      .o_empty        (o_fifo_empty[1]  ),
      .o_almost_full  (),
      .o_full         (o_fifo_full[1]   ),
      .slave_if       (slicer_if[0]     ),
      .master_if      (request_if       )
    );
  end

//--------------------------------------------------------------
//  Output Control
//--------------------------------------------------------------
  localparam  int PACKET_COUNT_WIDTH  = $clog2(COMMAND_DEPTH + 1);

  logic [1:0]                     write_packet_count_up_down;
  logic [PACKET_COUNT_WIDTH-1:0]  write_packet_count;
  logic [1:0]                     write_packet_done;
  logic                           write_ready;
  logic [2:0]                     write_done;

  always_comb begin
    write_packet_count_up_down[1] = slicer_if[0].write_data_last_ack();
    write_packet_count_up_down[0] = request_if.write_data_last_ack();
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      write_packet_count  <= '0;
    end
    else if (i_clear) begin
      write_packet_count  <= '0;
    end
    else if (write_packet_count_up_down == 2'b10) begin
      write_packet_count  <= write_packet_count + PACKET_COUNT_WIDTH'(1);
    end
    else if (write_packet_count_up_down == 2'b01) begin
      write_packet_count  <= write_packet_count - PACKET_COUNT_WIDTH'(1);
    end
  end

  always_comb begin
    write_done[0] = request_if.command_with_data_ack() && request_if.write_data_last_ack();
    write_done[1] = request_if.command_with_data_ack() && write_packet_done[1];
    write_done[2] = write_packet_done[0]               && request_if.write_data_last_ack();
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      write_packet_done <= '0;
    end
    else if (i_clear || (write_done != '0)) begin
      write_packet_done <= '0;
    end
    else begin
      if (request_if.command_with_data_ack()) begin
        write_packet_done[0]  <= '1;
      end
      if (request_if.write_data_last_ack()) begin
        write_packet_done[1]  <= '1;
      end
    end
  end

  always_comb begin
    write_ready =
      (write_packet_done[0] || request_if.command_with_data_valid()) &&
      (write_packet_count > PACKET_COUNT_WIDTH'(0));

    if (write_ready) begin
      request_if.scmd_accept    = (!write_packet_done[0]) && slicer_if[1].scmd_accept;
      slicer_if[1].mcmd_valid   = (!write_packet_done[0]) && request_if.mcmd_valid;
      request_if.sdata_accept   = (!write_packet_done[1]) && slicer_if[1].sdata_accept;
      slicer_if[1].mdata_valid  = (!write_packet_done[1]) && request_if.mdata_valid;
    end
    else if (request_if.is_command_no_data()) begin
      request_if.scmd_accept    = (!write_packet_done[0]) && slicer_if[1].scmd_accept;
      slicer_if[1].mcmd_valid   = (!write_packet_done[0]) && request_if.mcmd_valid;
      request_if.sdata_accept   = '0;
      slicer_if[1].mdata_valid  = '0;
    end
    else begin
      request_if.scmd_accept    = '0;
      slicer_if[1].mcmd_valid   = '0;
      request_if.sdata_accept   = '0;
      slicer_if[1].mdata_valid  = '0;
    end

    slicer_if[1].put_request(request_if.get_request());
  end

  always_comb begin
    slicer_if[1].mresp_accept = slicer_if[0].mresp_accept;
    slicer_if[0].sresp_valid  = slicer_if[1].sresp_valid;
    slicer_if[0].put_response(slicer_if[1].get_response());
  end

  pzcorebus_slicer #(
    .BUS_CONFIG           (BUS_CONFIG           ),
    .REQUEST_VALID        (MASTER_SLICER[0]     ),
    .RESPONSE_VALID       (MASTER_SLICER[1]     ),
    .REQUEST_SVA_CHECKER  (1                    ),
    .RESPONSE_SVA_CHECKER (RESPONSE_SVA_CHECKER )
  ) u_master_slicer (
    .i_clk      (i_clk        ),
    .i_rst_n    (i_rst_n      ),
    .slave_if   (slicer_if[1] ),
    .master_if  (master_if    )
  );
endmodule
