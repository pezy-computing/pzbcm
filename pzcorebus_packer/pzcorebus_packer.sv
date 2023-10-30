//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_packer
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG      = '0,
  parameter int               COMMAND_DEPTH   = 1,
  parameter int               DATA_DEPTH      = get_max_burst_length(BUS_CONFIG),
  parameter bit [1:0]         MASTER_SLICER   = '0,
  parameter type              SRAM_CONFIG     = logic,
  parameter int               READ_LATENCY    = 1,
  parameter int               SRAM_ID         = 0
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
  pzcorebus_if #(BUS_CONFIG)  bus_if[4]();

  pzcorebus_connector u_connector (
    slave_if, bus_if[0]
  );

  always_comb begin
    bus_if[0].sresp_valid   = bus_if[1].sresp_valid;
    bus_if[1].mresp_accept  = bus_if[0].mresp_accept;
    bus_if[0].put_response(bus_if[1].get_response());
  end

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
    .slave_if       (bus_if[0]        ),
    .master_if      (bus_if[1]        )
  );

//--------------------------------------------------------------
//  Write Data FIFO
//--------------------------------------------------------------
  pzcorebus_packer_data_fifo #(
    .BUS_CONFIG   (BUS_CONFIG   ),
    .DEPTH        (DATA_DEPTH   ),
    .SRAM_CONFIG  (SRAM_CONFIG  ),
    .READ_LATENCY (READ_LATENCY ),
    .SRAM_ID      (SRAM_ID      )
  ) u_data_fifo (
    .i_clk          (i_clk            ),
    .i_rst_n        (i_rst_n          ),
    .i_clear        (i_clear          ),
    .o_fifo_empty   (o_fifo_empty[1]  ),
    .o_fifo_full    (o_fifo_full[1]   ),
    .i_sram_config  (i_sram_config    ),
    .slave_if       (bus_if[0]        ),
    .master_if      (bus_if[1]        )
  );

//--------------------------------------------------------------
//  Output Control
//--------------------------------------------------------------
  localparam  int PACKET_COUNT_WIDTH  = $clog2(COMMAND_DEPTH + 1);

  logic                           write_packet_count_up;
  logic                           write_packet_count_down;
  logic [PACKET_COUNT_WIDTH-1:0]  write_packet_count;

  always_comb begin
    write_packet_count_up   = bus_if[0].write_data_last_ack();
    write_packet_count_down = bus_if[1].write_data_last_ack();
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      write_packet_count  <= '0;
    end
    else if (i_clear) begin
      write_packet_count  <= '0;
    end
    else if (write_packet_count_up && (!write_packet_count_down)) begin
      write_packet_count  <= write_packet_count + PACKET_COUNT_WIDTH'(1);
    end
    else if (write_packet_count_down && (!write_packet_count_up)) begin
      write_packet_count  <= write_packet_count - PACKET_COUNT_WIDTH'(1);
    end
  end

  always_comb begin
    if (!bus_if[1].mcmd[PZCOREBUS_WITH_DATA_BIT]) begin
      bus_if[2].mcmd_valid    = bus_if[1].mcmd_valid;
      bus_if[1].scmd_accept   = bus_if[2].scmd_accept;
      bus_if[2].mdata_valid   = bus_if[1].mdata_valid;
      bus_if[1].sdata_accept  = bus_if[2].sdata_accept;
    end
    else if ((write_packet_count != '0) || write_packet_count_up) begin
      bus_if[2].mcmd_valid    = bus_if[1].mcmd_valid;
      bus_if[1].scmd_accept   = bus_if[2].scmd_accept;
      bus_if[2].mdata_valid   = bus_if[1].mdata_valid;
      bus_if[1].sdata_accept  = bus_if[2].sdata_accept;
    end
    else begin
      bus_if[2].mcmd_valid    = '0;
      bus_if[1].scmd_accept   = '0;
      bus_if[2].mdata_valid   = '0;
      bus_if[1].sdata_accept  = '0;
    end
    bus_if[2].put_request(bus_if[1].get_request());
  end

  always_comb begin
    bus_if[1].sresp_valid   = bus_if[2].sresp_valid;
    bus_if[2].mresp_accept  = bus_if[1].mresp_accept;
    bus_if[1].put_response(bus_if[2].get_response());
  end

  pzcorebus_command_data_aligner #(
    .BUS_CONFIG (BUS_CONFIG ),
    .SLAVE_FIFO (0          )
  ) u_aligner (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (bus_if[2]  ),
    .master_if  (bus_if[3]  )
  );

  pzcorebus_slicer #(
    .BUS_CONFIG     (BUS_CONFIG       ),
    .REQUEST_VALID  (MASTER_SLICER[0] ),
    .RESPONSE_VALID (MASTER_SLICER[1] )
  ) u_slicer (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (bus_if[3]  ),
    .master_if  (master_if  )
  );
endmodule
