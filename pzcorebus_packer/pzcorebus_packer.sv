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
  parameter bit [1:0]         MASTER_SLICER   = '0
)(
  input   var         i_clk,
  input   var         i_rst_n,
  input   var         i_clear,
  output  var [1:0]   o_fifo_empty,
  output  var [1:0]   o_fifo_full,
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  typedef logic [get_packed_command_width(BUS_CONFIG)-1:0]  pzcorebus_packed_command;

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
  logic                           command_fifo_push;
  logic                           command_fifo_pop;
  pzcorebus_packed_command  [1:0] command_fifo_data;
  logic                           command_fifo_empty;
  logic                           command_fifo_full;

  always_comb begin
    o_fifo_empty[0] = command_fifo_empty;
    o_fifo_full[0]  = command_fifo_full;
  end

  always_comb begin
    bus_if[0].scmd_accept = !command_fifo_full;
    command_fifo_push     = bus_if[0].command_ack();
    command_fifo_data[0]  = bus_if[0].get_packed_command();
  end

  always_comb begin
    command_fifo_pop      = bus_if[1].command_ack();
    bus_if[1].mcmd_valid  = !command_fifo_empty;
    bus_if[1].put_packed_command(command_fifo_data[1]);
  end

  pzbcm_fifo #(
    .TYPE         (pzcorebus_packed_command ),
    .DEPTH        (COMMAND_DEPTH            ),
    .FLAG_FF_OUT  (1                        ),
    .DATA_FF_OUT  (1                        )
  ) u_command_fifo (
    .i_clk          (i_clk                ),
    .i_rst_n        (i_rst_n              ),
    .i_clear        (i_clear              ),
    .o_empty        (command_fifo_empty   ),
    .o_almost_full  (),
    .o_full         (command_fifo_full    ),
    .o_word_count   (),
    .i_push         (command_fifo_push    ),
    .i_data         (command_fifo_data[0] ),
    .i_pop          (command_fifo_pop     ),
    .o_data         (command_fifo_data[1] )
  );

//--------------------------------------------------------------
//  Write Data FIFO
//--------------------------------------------------------------
  pzcorebus_packer_data_fifo #(
    .BUS_CONFIG (BUS_CONFIG ),
    .DEPTH      (DATA_DEPTH )
  ) u_data_fifo (
    .i_clk        (i_clk            ),
    .i_rst_n      (i_rst_n          ),
    .i_clear      (i_clear          ),
    .o_fifo_empty (o_fifo_empty[1]  ),
    .o_fifo_full  (o_fifo_full[1]   ),
    .slave_if     (bus_if[0]        ),
    .master_if    (bus_if[1]        )
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
    .RELAX_MODE (0          ),
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
