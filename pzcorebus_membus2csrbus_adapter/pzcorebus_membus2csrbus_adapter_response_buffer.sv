//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_membus2csrbus_adapter_response_buffer
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  CSRBUS_CONFIG = '0,
  parameter int               ENTRIES       = 2,
  parameter bit [1:0]         MASTER_SLICER = '0
)(
  input var                               i_clk,
  input var                               i_rst_n,
  input var [CSRBUS_CONFIG.id_width-1:0]  i_base_id,
  input var                               i_wait_for_all_responses,
  pzcorebus_if.slave                      slave_if,
  pzcorebus_if.master                     master_if
);
  localparam  int ID_WIDTH    = CSRBUS_CONFIG.id_width;
  localparam  int INDEX_WIDTH = $clog2(ENTRIES);

  typedef struct packed {
    logic                                 busy;
    logic                                 sresp_valid;
    logic                                 serror;
    logic [CSRBUS_CONFIG.data_width-1:0]  sdata;
  } pzcorebus_response_entry;

  pzcorebus_response_entry  [ENTRIES-1:0] response_entries;
  pzcorebus_if #(CSRBUS_CONFIG)           csrbus_if();

//--------------------------------------------------------------
//  Request
//--------------------------------------------------------------
  logic [INDEX_WIDTH-1:0] request_index;
  logic [1:0]             request_ready;
  pzcorebus_command       command;

  always_comb begin
    request_ready[0]      = slave_if.is_posted_command();
    request_ready[1]      = get_non_posted_ready(request_index, response_entries, i_wait_for_all_responses);
    slave_if.scmd_accept  = (request_ready != '0) && csrbus_if.scmd_accept;
    csrbus_if.mcmd_valid  = (request_ready != '0) && slave_if.mcmd_valid;

    command     = slave_if.get_command();
    command.id  = i_base_id | ID_WIDTH'(request_index);
    csrbus_if.put_command(command);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      request_index <= INDEX_WIDTH'(0);
    end
    else if (slave_if.command_non_posted_ack()) begin
      if (request_index == INDEX_WIDTH'(ENTRIES - 1)) begin
        request_index <= INDEX_WIDTH'(0);
      end
      else begin
        request_index <= request_index + INDEX_WIDTH'(1);
      end
    end
  end

  always_comb begin
    slave_if.sdata_accept   = '0;
    csrbus_if.mdata_valid   = '0;
    csrbus_if.mdata_byteen  = '0;
    csrbus_if.mdata_last    = '0;
  end

  function automatic logic get_non_posted_ready(
    logic [INDEX_WIDTH-1:0]                 request_index,
    pzcorebus_response_entry  [ENTRIES-1:0] response_entries,
    logic                                   wait_for_all_responses
  );
    logic [ENTRIES-1:0] response_busy;

    for (int i = 0;i < ENTRIES;++i) begin
      response_busy[i]  = response_entries[i].busy;
    end

    return (!response_entries[request_index].busy) && ((!wait_for_all_responses) || (response_busy == '0));
  endfunction

//--------------------------------------------------------------
//  Response
//--------------------------------------------------------------
  pzcorebus_response_entry  response_entry;
  logic [INDEX_WIDTH-1:0]   response_index;

  always_comb begin
    response_entry        = response_entries[response_index];
    slave_if.sresp_valid  = response_entry.sresp_valid;
    slave_if.sresp        = pzcorebus_response_type'(0);
    slave_if.sid          = ID_WIDTH'(0);
    slave_if.serror       = response_entry.serror;
    slave_if.sdata        = response_entry.sdata;
    slave_if.sinfo        = '0;
    slave_if.sresp_uniten = '0;
    slave_if.sresp_last   = '0;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      response_index  <= INDEX_WIDTH'(0);
    end
    else if (slave_if.response_ack()) begin
      if (response_index == INDEX_WIDTH'(ENTRIES - 1)) begin
        response_index  <= INDEX_WIDTH'(0);
      end
      else begin
        response_index  <= response_index + INDEX_WIDTH'(1);
      end
    end
  end

//--------------------------------------------------------------
//  Response entry
//--------------------------------------------------------------
  always_comb begin
    csrbus_if.mresp_accept  = '1;
  end

  for (genvar i = 0;i < ENTRIES;++i) begin : g_response_entry
    localparam  bit [INDEX_WIDTH-1:0] INDEX = i;

    logic init_entry;
    logic fill_entry;
    logic clear_entry;

    always_comb begin
      init_entry  = csrbus_if.command_non_posted_ack() && (request_index == INDEX);
      fill_entry  = csrbus_if.response_ack() && (INDEX_WIDTH'(csrbus_if.sid) == INDEX);
      clear_entry = slave_if.response_ack() && (response_index == INDEX);
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        response_entries[i] <= '0;
      end
      else if (init_entry) begin
        response_entries[i].busy  <= '1;
      end
      else if (fill_entry) begin
        response_entries[i].sresp_valid <= '1;
        response_entries[i].serror      <= csrbus_if.serror;
        response_entries[i].sdata       <= csrbus_if.sdata;
      end
      else if (clear_entry) begin
        response_entries[i].busy        <= '0;
        response_entries[i].sresp_valid <= '0;
      end
    end
  end

//--------------------------------------------------------------
//  Slicer
//--------------------------------------------------------------
  pzcorebus_slicer #(
    .BUS_CONFIG     (CSRBUS_CONFIG    ),
    .REQUEST_VALID  (MASTER_SLICER[0] ),
    .RESPONSE_VALID (MASTER_SLICER[1] )
  ) u_slicer (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (csrbus_if  ),
    .master_if  (master_if  )
  );
endmodule
