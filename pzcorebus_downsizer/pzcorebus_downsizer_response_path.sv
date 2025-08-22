//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_downsizer_response_path
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  SLAVE_CONFIG          = '0,
  parameter pzcorebus_config  MASTER_CONFIG         = '0,
  parameter int               CONVERSION_RATIO      = 2,
  parameter bit               ALLIGNED_ACCESS_ONLY  = 0
)(
  input var                     i_clk,
  input var                     i_rst_n,
  pzcorebus_if.response_slave   slave_if,
  pzcorebus_if.response_master  master_if
);
  typedef logic [SLAVE_CONFIG.unit_data_width-1:0]              pzcorebus_unit_data;
  typedef logic [get_response_info_width(SLAVE_CONFIG, 1)-1:0]  pzcorebus_response_info;
  typedef logic [get_unit_enable_width(SLAVE_CONFIG, 1)-1:0]    pzcorebus_unit_enable;

  localparam  int UNIT_DATA_WIDTH   = SLAVE_CONFIG.unit_data_width;
  localparam  int MAX_UNIT_SIZE     = SLAVE_CONFIG.max_data_width / UNIT_DATA_WIDTH;
  localparam  int SLAVE_UNIT_SIZE   = SLAVE_CONFIG.data_width     / UNIT_DATA_WIDTH;
  localparam  int MASTER_UNIT_SIZE  = MASTER_CONFIG.data_width    / UNIT_DATA_WIDTH;

  logic [SLAVE_UNIT_SIZE-1:0]               unit_enable;
  logic                                     tail_unit_enable;
  logic                                     response_busy;
  logic [2:0]                               response_filled;
  logic [1:0]                               serror;
  pzcorebus_unit_data [SLAVE_UNIT_SIZE-1:0] sdata;
  pzcorebus_response_info [1:0]             sinfo;
  pzcorebus_unit_enable [1:0]               sresp_uniten;

  if (ALLIGNED_ACCESS_ONLY) begin : g_unit_enable
    logic [CONVERSION_RATIO-1:0]  response_stored;

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        response_stored <= '0;
      end
      else if (slave_if.response_ack()) begin
        response_stored <= '0;
      end
      else if (master_if.response_ack()) begin
        response_stored <=
          CONVERSION_RATIO'({response_stored, 1'b1});
      end
    end

    always_comb begin
      for (int i = 0;i < CONVERSION_RATIO;++i) begin
        unit_enable[MASTER_UNIT_SIZE*i+:MASTER_UNIT_SIZE] =
          (!response_stored[i]) ? '1 : '0;
      end

      tail_unit_enable  =
        (response_stored[CONVERSION_RATIO-1] == '0) &&
        (response_stored[CONVERSION_RATIO-2] == '1);
    end
  end
  else begin : g_unit_enable
    always_comb begin
      for (int i = 0;i < SLAVE_UNIT_SIZE;++i) begin
        unit_enable[i]  = get_unit_enable(master_if.sresp_uniten, i);
      end

      tail_unit_enable  = unit_enable[SLAVE_UNIT_SIZE-1];
    end
  end

  function automatic logic get_unit_enable(
    pzcorebus_unit_enable sresp_uniten,
    int                   unit_index
  );
    logic [(MAX_UNIT_SIZE/SLAVE_UNIT_SIZE)-1:0] uniten;

    for (int i = 0;i < $bits(uniten);++i) begin
      uniten[i] = sresp_uniten[SLAVE_UNIT_SIZE*i+unit_index];
    end

    return |{1'b0, uniten};
  endfunction

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      response_busy <= '0;
    end
    else if (slave_if.response_ack()) begin
      response_busy <= '0;
    end
    else if (master_if.response_ack()) begin
      response_busy <= '1;
    end
  end

  always_comb begin
    serror[0]       = serror[1]       | master_if.serror;
    sresp_uniten[0] = sresp_uniten[1] | master_if.sresp_uniten;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      serror[1]       <= '0;
      sresp_uniten[1] <= '0;
    end
    else if (slave_if.response_ack()) begin
      serror[1]       <= '0;
      sresp_uniten[1] <= '0;
    end
    else if (master_if.response_ack()) begin
      serror[1]       <= serror[0];
      sresp_uniten[1] <= sresp_uniten[0];
    end
  end

  if (SLAVE_CONFIG.response_info_width > 0) begin : g_sresp_info
    always_comb begin
      sinfo[0]  = (response_busy) ? sinfo[1] : master_if.sinfo;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        sinfo[1]  <= '0;
      end
      else if ((!response_busy) && master_if.response_ack()) begin
        sinfo[1]  <= sinfo[0];
      end
    end
  end
  else begin : g_sresp_info
    always_comb begin
      sinfo[0]  = '0;
      sinfo[1]  = '0;
    end
  end

  for (genvar i = 0;i < SLAVE_UNIT_SIZE;++i) begin : g_sdata
    localparam  int MASTER_UNIT_INDEX = i % MASTER_UNIT_SIZE;
    localparam  int MASTER_LSB        = UNIT_DATA_WIDTH * (MASTER_UNIT_INDEX + 0) - 0;
    localparam  int MASTER_MSB        = UNIT_DATA_WIDTH * (MASTER_UNIT_INDEX + 1) - 1;

    if (i == (SLAVE_UNIT_SIZE - 1)) begin : g
      always_comb begin
        sdata[i]  = master_if.sdata[MASTER_MSB:MASTER_LSB];
      end
    end
    else begin : g
      pzcorebus_unit_data sdata_latched;

      always_comb begin
        if (unit_enable[i]) begin
          sdata[i]  = master_if.sdata[MASTER_MSB:MASTER_LSB];
        end
        else begin
          sdata[i]  = sdata_latched;
        end
      end

      always_ff @(posedge i_clk) begin
        if (master_if.response_ack()) begin
          sdata_latched <= sdata[i];
        end
      end
    end
  end

  always_comb begin
    response_filled[0]  = master_if.sresp      == PZCOREBUS_RESPONSE;
    response_filled[1]  = master_if.sresp_last != '0;
    response_filled[2]  = tail_unit_enable;

    if (response_filled != '0) begin
      slave_if.sresp_valid    = master_if.sresp_valid;
      master_if.mresp_accept  = slave_if.mresp_accept;
    end
    else begin
      slave_if.sresp_valid    = '0;
      master_if.mresp_accept  = '1;
    end

    slave_if.sresp        = master_if.sresp;
    slave_if.sid          = master_if.sid;
    slave_if.serror       = serror[0];
    slave_if.sdata        = sdata;
    slave_if.sinfo        = sinfo[0];
    slave_if.sresp_uniten = sresp_uniten[0];
    slave_if.sresp_last   = master_if.sresp_last;
  end
endmodule
