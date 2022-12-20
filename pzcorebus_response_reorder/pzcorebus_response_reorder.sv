//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_response_reorder
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config                BUS_CONFIG    = '0,
  parameter int                             ENTRIES       = 4,
  parameter bit [BUS_CONFIG.data_width-1:0] ERROR_DATA    = 'hdead_aaaa,
  parameter bit                             SLAVE_SLICER  = 0,
  parameter bit                             MASTER_SLICER = 0,
  parameter int                             TIMEOUT_WIDTH = 32
)(
  input var                           i_clk,
  input var                           i_rst_n,
  input var [BUS_CONFIG.id_width-1:0] i_base_id,
  input var                           i_timeout_enable,
  input var [TIMEOUT_WIDTH-1:0]       i_timeout_cycle,
  pzcorebus_if.slave                  slave_if,
  pzcorebus_if.master                 master_if
);
  localparam  int INDEX_WIDTH = $clog2(ENTRIES);

  typedef struct packed {
    logic                             busy;
    logic                             sresp_valid;
    pzcorebus_response_type           sresp;
    logic [BUS_CONFIG.id_width-1:0]   sid;
    logic                             serror;
    logic [BUS_CONFIG.data_width-1:0] sdata;
  } pzcorebus_response_entry;

  initial begin
    assert (BUS_CONFIG.profile == PZCOREBUS_CSR);
  end

  logic [INDEX_WIDTH-1:0]                 request_index;
  logic [INDEX_WIDTH-1:0]                 response_index;
  pzcorebus_response_entry  [ENTRIES-1:0] response_entries;
  logic [ENTRIES-1:0]                     active_response;
  logic                                   timeout;
  logic [TIMEOUT_WIDTH-1:0]               timeout_count;
  pzcorebus_command                       command;
  pzcorebus_response_entry                response_entry;
  pzcorebus_if #(BUS_CONFIG)              bus_if[2]();

//--------------------------------------------------------------
//  Slave slicer
//--------------------------------------------------------------
  pzcorebus_slicer #(
    .BUS_CONFIG     (BUS_CONFIG   ),
    .STAGES         (1            ),
    .REQUEST_VALID  (SLAVE_SLICER ),
    .RESPONSE_VALID (SLAVE_SLICER )
  ) u_slave_slicer (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (slave_if   ),
    .master_if  (bus_if[0]  )
  );

//--------------------------------------------------------------
//  Request
//--------------------------------------------------------------
  always_comb begin
    if (bus_if[0].is_posted_command() || (!response_entries[request_index].busy)) begin
      bus_if[0].scmd_accept = bus_if[1].scmd_accept;
      bus_if[1].mcmd_valid  = bus_if[0].mcmd_valid;
    end
    else  begin
      bus_if[0].scmd_accept = '0;
      bus_if[1].mcmd_valid  = '0;
    end

    command     = bus_if[0].get_command();
    command.id  = i_base_id | BUS_CONFIG.id_width'(request_index);
    bus_if[1].put_command(command);
  end

  always_comb begin
    bus_if[0].sdata_accept  = '0;
    bus_if[1].mdata_valid   = '0;
    bus_if[1].mdata_byteen  = '0;
    bus_if[1].mdata_last    = '0;
  end

//--------------------------------------------------------------
//  Response
//--------------------------------------------------------------
  always_comb begin
    response_entry        = response_entries[response_index];
    bus_if[0].sresp_valid = response_entry.sresp_valid;
    bus_if[0].sresp       = response_entry.sresp;
    bus_if[0].sid         = response_entry.sid;
    bus_if[0].serror      = response_entry.serror;
    bus_if[0].sdata       = (response_entry.serror) ? ERROR_DATA : response_entry.sdata;
    bus_if[0].sinfo       = '0;
  end

  always_comb begin
    bus_if[1].mresp_accept  = '1;
  end

//--------------------------------------------------------------
//  Response entry
//--------------------------------------------------------------
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      request_index <= INDEX_WIDTH'(0);
    end
    else if (bus_if[0].command_non_posted_ack()) begin
      if (request_index == INDEX_WIDTH'(ENTRIES - 1)) begin
        request_index <= INDEX_WIDTH'(0);
      end
      else begin
        request_index <= request_index + INDEX_WIDTH'(1);
      end
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      response_index  <= INDEX_WIDTH'(0);
    end
    else if (bus_if[0].response_ack()) begin
      if (response_index == INDEX_WIDTH'(ENTRIES - 1)) begin
        response_index  <= INDEX_WIDTH'(0);
      end
      else begin
        response_index  <= response_index + INDEX_WIDTH'(1);
      end
    end
  end

  for (genvar i = 0;i < ENTRIES;++i) begin : g_response_entry
    logic initialize_entry;
    logic update_entry;
    logic clear_entry;

    always_comb begin
      initialize_entry  =
        bus_if[0].command_non_posted_ack() && (request_index == INDEX_WIDTH'(i));
      update_entry  =
        bus_if[1].response_ack() && (INDEX_WIDTH'(bus_if[1].sid) == INDEX_WIDTH'(i));
      clear_entry =
        bus_if[0].response_ack() && (response_index == INDEX_WIDTH'(i));
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        response_entries[i] <= '0;
      end
      else if (initialize_entry) begin
        response_entries[i].busy        <= '1;
        response_entries[i].sresp_valid <= '0;
        response_entries[i].sid         <= bus_if[0].mid;
      end
      else if (response_entries[i].busy && (update_entry || timeout)) begin
        response_entries[i].sresp_valid <= '1;
        response_entries[i].sresp       <= bus_if[1].sresp;
        response_entries[i].serror      <= bus_if[1].serror || timeout;
        response_entries[i].sdata       <= bus_if[1].sdata;
      end
      else if (clear_entry) begin
        response_entries[i].busy        <= '0;
        response_entries[i].sresp_valid <= '0;
      end
    end

    always_comb begin
      active_response[i]  = response_entries[i].busy && (!response_entries[i].sresp_valid);
    end
  end

//--------------------------------------------------------------
//  Timeout
//--------------------------------------------------------------
  always_comb begin
    timeout = i_timeout_enable && (timeout_count == i_timeout_cycle);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      timeout_count <= TIMEOUT_WIDTH'(0);
    end
    else if (i_timeout_enable) begin
      if (bus_if[0].command_non_posted_ack()) begin
        timeout_count <= TIMEOUT_WIDTH'(0);
      end
      else if (active_response != '0) begin
        timeout_count <= timeout_count + TIMEOUT_WIDTH'(1);
      end
    end
  end

//--------------------------------------------------------------
//  Master slicer
//--------------------------------------------------------------
  pzcorebus_slicer #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .STAGES         (1              ),
    .REQUEST_VALID  (MASTER_SLICER  ),
    .RESPONSE_VALID (MASTER_SLICER  )
  ) u_master_slicer (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (bus_if[1]  ),
    .master_if  (master_if  )
  );
endmodule
