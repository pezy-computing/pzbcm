//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_upsizer_response_path
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  SLAVE_CONFIG  = '0,
  parameter pzcorebus_config  MASTER_CONFIG = '0
)(
  input var                     i_clk,
  input var                     i_rst_n,
  pzcorebus_if.response_slave   slave_if,
  pzcorebus_if.response_master  master_if
);
  localparam  int UNIT_WIDTH        = SLAVE_CONFIG.unit_data_width;
  localparam  int SLAVE_DATA_WIDTH  = SLAVE_CONFIG.data_width;
  localparam  int MASTER_DATA_WIDTH = MASTER_CONFIG.data_width;
  localparam  int MAX_DATA_SIZE     = SLAVE_CONFIG.max_data_width / UNIT_WIDTH;
  localparam  int SLAVE_DATA_SIZE   = SLAVE_DATA_WIDTH  / UNIT_WIDTH;
  localparam  int MASTER_DATA_SIZE  = MASTER_DATA_WIDTH / UNIT_WIDTH;
  localparam  int SLAVE_RATIO       = MAX_DATA_SIZE / SLAVE_DATA_SIZE;
  localparam  int MASTER_RATIO      = MAX_DATA_SIZE / MASTER_DATA_SIZE;

  typedef logic [get_unit_enable_width(MASTER_CONFIG, 1)-1:0] pzcorebus_unit_enable;
  typedef logic [$clog2(MAX_DATA_SIZE)-1:0]                   pzcorebus_unit_index;
  typedef logic [$clog2(SLAVE_DATA_SIZE)-1:0]                 pzcorebus_slave_index;
  typedef logic [$clog2(MASTER_DATA_SIZE)-1:0]                pzcorebus_master_index;
  typedef logic [SLAVE_CONFIG.data_width-1:0]                 pzcorebus_slave_data;
  typedef logic [MASTER_CONFIG.data_width-1:0]                pzcorebus_master_data;

  logic                       sresp_busy;
  pzcorebus_unit_index        start_index;
  pzcorebus_unit_index        end_index;
  pzcorebus_unit_index  [1:0] sresp_index;
  pzcorebus_slave_index       slave_index;
  pzcorebus_master_index      master_index;

//--------------------------------------------------------------
//  State
//--------------------------------------------------------------
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      sresp_busy  <= '0;
    end
    else if (slave_if.response_last_burst_ack()) begin
      sresp_busy  <= '0;
    end
    else if (slave_if.response_ack()) begin
      sresp_busy  <= '1;
    end
  end

  always_comb begin
    start_index = get_start_index(master_if.sresp_uniten);
    end_index   = get_end_index(master_if.sresp_uniten);
  end

  always_comb begin
    sresp_index[0]  = (!sresp_busy) ? start_index : sresp_index[1];
    slave_index     = pzcorebus_slave_index'(sresp_index[0]);
    master_index    = pzcorebus_master_index'(sresp_index[0]);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      sresp_index[1]  <= pzcorebus_unit_index'(0);
    end
    else if (slave_if.response_ack()) begin
      sresp_index[1]  <=
        sresp_index[0] + pzcorebus_unit_index'(SLAVE_DATA_SIZE);
    end
  end

  function automatic pzcorebus_unit_index get_start_index(
    pzcorebus_unit_enable unit_enable
  );
    pzcorebus_unit_index  index;

    index = pzcorebus_unit_index'(0);
    for (int i = 0;i < MAX_DATA_SIZE;i += SLAVE_DATA_SIZE) begin
      if (unit_enable[i+:SLAVE_DATA_SIZE] != '0) begin
        index = pzcorebus_unit_index'(i);
        break;
      end
    end

    return index;
  endfunction

  function automatic pzcorebus_unit_index get_end_index(
    pzcorebus_unit_enable unit_enable
  );
    pzcorebus_unit_index  index;

    index = pzcorebus_unit_index'(MAX_DATA_SIZE - SLAVE_DATA_SIZE);
    for (int i = MAX_DATA_SIZE - SLAVE_DATA_SIZE;i >= 0;i -= SLAVE_DATA_SIZE) begin
      if (unit_enable[i+:SLAVE_DATA_SIZE] != '0) begin
        index = pzcorebus_unit_index'(i);
        break;
      end
    end

    return index;
  endfunction

//--------------------------------------------------------------
//  Bus access
//--------------------------------------------------------------
  logic [1:0] response_accept;

  always_comb begin
    response_accept[0]  = sresp_index[0]  == end_index;
    response_accept[1]  = master_if.sresp == PZCOREBUS_RESPONSE;

    if (response_accept != '0) begin
      master_if.mresp_accept  = slave_if.mresp_accept;
      slave_if.sresp_valid    = master_if.sresp_valid;
      slave_if.sresp_last     = master_if.sresp_last;
    end
    else begin
      master_if.mresp_accept  = '0;
      slave_if.sresp_valid    = master_if.sresp_valid;
      slave_if.sresp_last     = '0;
    end

    slave_if.sresp        = master_if.sresp;
    slave_if.sid          = master_if.sid;
    slave_if.serror       = master_if.serror;
    slave_if.sdata        = master_if.sdata[UNIT_WIDTH*master_index+:SLAVE_DATA_WIDTH];
    slave_if.sinfo        = master_if.sinfo;
    slave_if.sresp_uniten = get_sresp_uniten(sresp_index, master_if.sresp_uniten);
  end

  function automatic pzcorebus_unit_enable get_sresp_uniten(
    pzcorebus_unit_index  sresp_index,
    pzcorebus_unit_enable sresp_uniten
  );
    pzcorebus_unit_enable uniten;
    uniten                                = '0;
    uniten[sresp_index+:SLAVE_DATA_SIZE]  = sresp_uniten[sresp_index+:SLAVE_DATA_SIZE];
    return uniten;
  endfunction
endmodule
