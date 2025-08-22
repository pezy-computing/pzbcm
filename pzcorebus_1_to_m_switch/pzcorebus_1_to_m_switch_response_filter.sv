//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//
//========================================
module pzcorebus_1_to_m_switch_response_filter
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG                    = '0,
  parameter int               MASTERS                       = 2,
  parameter int               MAX_NON_POSTED_WRITE_REQUESTS = 1,
  parameter bit [1:0]         SLAVE_FIFO                    = '0,
  parameter int               COMMAND_DEPTH                 = 2,
  parameter int               RESPONSE_DEPTH                = 2
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  function automatic int calc_width(int v);
    return (v > 1) ? $clog2(v) : 1;
  endfunction

  localparam  int ID_WIDTH              = BUS_CONFIG.id_width;
  localparam  int REQUEST_INDEX_WIDTH   = calc_width(MAX_NON_POSTED_WRITE_REQUESTS);
  localparam  int RESPONSE_COUNT_WIDTH  = calc_width(MASTERS);

  typedef struct packed {
    logic                             busy;
    logic [ID_WIDTH-1:0]              id;
    logic                             error;
    logic [RESPONSE_COUNT_WIDTH-1:0]  count;
  } pzcorebus_1_to_m_switch_request_info;

  pzcorebus_if #(BUS_CONFIG)                                                bus_if[2]();
  logic [2:0]                                                               request_ready;
  logic                                                                     np_write_ack;
  logic [1:0]                                                               response_ready;
  pzcorebus_1_to_m_switch_request_info [MAX_NON_POSTED_WRITE_REQUESTS-1:0]  request_info;
  logic [REQUEST_INDEX_WIDTH-1:0]                                           request_index;
  logic [MAX_NON_POSTED_WRITE_REQUESTS-1:0]                                 id_busy;
  logic [MAX_NON_POSTED_WRITE_REQUESTS-1:0]                                 response_last;
  logic [MAX_NON_POSTED_WRITE_REQUESTS-1:0]                                 response_error;

//--------------------------------------------------------------
//  Slave FIFO
//--------------------------------------------------------------
  pzcorebus_fifo #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .COMMAND_DEPTH  (COMMAND_DEPTH  ),
    .COMMAND_VALID  (SLAVE_FIFO[0]  ),
    .RESPONSE_DEPTH (RESPONSE_DEPTH ),
    .RESPONSE_VALID (SLAVE_FIFO[1]  )
  ) u_slave_fifo (
    .i_clk          (i_clk      ),
    .i_rst_n        (i_rst_n    ),
    .i_clear        ('0         ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (slave_if   ),
    .master_if      (bus_if[0]  )
  );

//--------------------------------------------------------------
//  Request path
//--------------------------------------------------------------
  always_comb begin
    request_ready[2]  = !bus_if[0].is_non_posted_write_access_command();
    request_ready[1]  = !request_info[request_index].busy;
    request_ready[0]  = id_busy == '0;

    if (request_ready inside {3'b1??, 3'b011}) begin
      bus_if[0].scmd_accept = bus_if[1].scmd_accept;
      bus_if[1].mcmd_valid  = bus_if[0].mcmd_valid;
    end
    else begin
      bus_if[0].scmd_accept = '0;
      bus_if[1].mcmd_valid  = '0;
    end

    bus_if[1].put_command(bus_if[0].get_command());
  end

  always_comb begin
    np_write_ack  = bus_if[0].command_ack() && (!request_ready[2]);
  end

  always_comb begin
    bus_if[0].sdata_accept  = '0;
    bus_if[1].mdata_valid   = '0;
    bus_if[1].mdata_byteen  = '0;
    bus_if[1].mdata_last    = '0;
  end

//--------------------------------------------------------------
//  Response path
//--------------------------------------------------------------
  always_comb begin
    response_ready[1] = bus_if[1].sresp == PZCOREBUS_RESPONSE_WITH_DATA;
    response_ready[0] = response_last != '0;

    if (response_ready != '0) begin
      bus_if[1].mresp_accept  = bus_if[0].mresp_accept;
      bus_if[0].sresp_valid   = bus_if[1].sresp_valid;
    end
    else begin
      bus_if[1].mresp_accept  = '1;
      bus_if[0].sresp_valid   = '0;
    end

    bus_if[0].sresp         = bus_if[1].sresp;
    bus_if[0].sid           = bus_if[1].sid;
    bus_if[0].serror        = bus_if[1].serror || (response_error != '0);
    bus_if[0].sdata         = bus_if[1].sdata;
    bus_if[0].sinfo         = bus_if[1].sinfo;
    bus_if[0].sresp_uniten  = '0;
    bus_if[0].sresp_last    = '0;
  end

//--------------------------------------------------------------
//  Master Slicer
//--------------------------------------------------------------
  pzcorebus_slicer #(
    .BUS_CONFIG (BUS_CONFIG )
  ) u_master_slicer (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (bus_if[1]  ),
    .master_if  (master_if  )
  );

//--------------------------------------------------------------
//  Request info
//--------------------------------------------------------------
  for (genvar i = 0;i < MAX_NON_POSTED_WRITE_REQUESTS;++i) begin : g_request_info
    logic [1:0] match_id;
    logic       command_ack;
    logic       response_ack;

    always_comb begin
      match_id[0]       = request_info[i].busy && (bus_if[0].mid == request_info[i].id);
      match_id[1]       = request_info[i].busy && (bus_if[1].sid == request_info[i].id);
      id_busy[i]        = match_id[0];
      response_last[i]  = match_id[1] && (request_info[i].count == RESPONSE_COUNT_WIDTH'(0));
      response_error[i] = match_id[1] && request_info[i].error;
    end

    always_comb begin
      command_ack   = np_write_ack && (request_index == REQUEST_INDEX_WIDTH'(i));
      response_ack  = bus_if[1].response_no_data_ack() && match_id[1];
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        request_info[i].busy  <= '0;
      end
      else if (response_ack && response_last[i]) begin
        request_info[i].busy  <= '0;
      end
      else if (command_ack) begin
        request_info[i].busy  <= '1;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        request_info[i].id  <= ID_WIDTH'(0);
      end
      else if (command_ack) begin
        request_info[i].id  <= bus_if[0].mid;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        request_info[i].error <= '0;
        request_info[i].count <= RESPONSE_COUNT_WIDTH'(0);
      end
      else if (command_ack) begin
        request_info[i].error <= '0;
        if (bus_if[0].mcmd == PZCOREBUS_WRITE_NON_POSTED) begin
          request_info[i].count <= RESPONSE_COUNT_WIDTH'(0);
        end
        else begin
          request_info[i].count <= RESPONSE_COUNT_WIDTH'(MASTERS - 1);
        end
      end
      else if (response_ack && (!response_last[i])) begin
        request_info[i].error <= request_info[i].error || bus_if[1].serror;
        request_info[i].count <= request_info[i].count - RESPONSE_COUNT_WIDTH'(1);
      end
    end
  end

  if (MAX_NON_POSTED_WRITE_REQUESTS > 1) begin : g_request_index
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        request_index <= REQUEST_INDEX_WIDTH'(0);
      end
      else if (np_write_ack) begin
        if (request_index == REQUEST_INDEX_WIDTH'(MAX_NON_POSTED_WRITE_REQUESTS - 1)) begin
          request_index <= REQUEST_INDEX_WIDTH'(0);
        end
        else begin
          request_index <= request_index + REQUEST_INDEX_WIDTH'(1);
        end
      end
    end
  end
  else begin : g_request_index
    always_comb begin
      request_index = REQUEST_INDEX_WIDTH'(0);
    end
  end
endmodule
