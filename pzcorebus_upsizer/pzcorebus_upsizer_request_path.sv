//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_upsizer_request_path
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  SLAVE_CONFIG      = '0,
  parameter pzcorebus_config  MASTER_CONFIG     = '0,
  parameter int               CONVERSION_RATIO  = 1
)(
  input var                   i_clk,
  input var                   i_rst_n,
  pzcorebus_if.request_slave  slave_if,
  pzcorebus_if.request_master master_if
);
  typedef logic [SLAVE_CONFIG.data_width-1:0]                 pzcorebus_data;
  typedef logic [get_byte_enable_width(SLAVE_CONFIG, 1)-1:0]  pzcorebus_byte_enable;

  localparam  int COUNTER_WIDTH = $clog2(CONVERSION_RATIO);
  localparam  int ADDRESS_LSB   = $clog2(SLAVE_CONFIG.data_width / 8);

  logic                     mdata_busy;
  logic [COUNTER_WIDTH-1:0] mdata_count;
  logic [COUNTER_WIDTH-1:0] mdata_count_latched;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      mdata_busy  <= '0;
    end
    else if (slave_if.write_data_last_ack()) begin
      mdata_busy  <= '0;
    end
    else if (slave_if.write_data_ack()) begin
      mdata_busy  <= '1;
    end
  end

  always_comb begin
    if (slave_if.mcmd_valid && (!mdata_busy)) begin
      mdata_count = (slave_if.mcmd inside {
        PZCOREBUS_ATOMIC, PZCOREBUS_ATOMIC_NON_POSTED
      }) ? COUNTER_WIDTH'(0) : slave_if.maddr[ADDRESS_LSB+:COUNTER_WIDTH];
    end
    else begin
      mdata_count = mdata_count_latched;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      mdata_count_latched <= '0;
    end
    else if (slave_if.write_data_ack()) begin
      mdata_count_latched <= mdata_count + COUNTER_WIDTH'(1);
    end
    else if (slave_if.command_with_data_ack()) begin
      mdata_count_latched <= mdata_count;
    end
  end

  pzcorebus_data  [CONVERSION_RATIO-1:0]        mdata;
  pzcorebus_byte_enable [CONVERSION_RATIO-1:0]  mdata_byteen;

  for (genvar i = 0;i < CONVERSION_RATIO;++i) begin : g_mdata
    logic match_count;

    always_comb begin
      match_count = (mdata_count == COUNTER_WIDTH'(i));
    end

    if (i == (CONVERSION_RATIO - 1)) begin : g
      always_comb begin
        mdata[i]        = slave_if.mdata;
        mdata_byteen[i] = (match_count) ? slave_if.mdata_byteen : '0;
      end
    end
    else begin : g
      pzcorebus_data  [CONVERSION_RATIO-1:0]        mdata_latched;
      pzcorebus_byte_enable [CONVERSION_RATIO-1:0]  mdata_byteen_latched;

      always_comb begin
        if (match_count) begin
          mdata[i]        = slave_if.mdata;
          mdata_byteen[i] = slave_if.mdata_byteen;
        end
        else begin
          mdata[i]        = mdata_latched;
          mdata_byteen[i] = mdata_byteen_latched;
        end
      end

      always_ff @(posedge i_clk) begin
        if (slave_if.write_data_ack() && match_count) begin
          mdata_latched <= slave_if.mdata;
        end
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          mdata_byteen_latched  <= '0;
        end
        else if (master_if.write_data_ack()) begin
          mdata_byteen_latched  <= '0;
        end
        else if (slave_if.write_data_ack() && match_count) begin
          mdata_byteen_latched  <= slave_if.mdata_byteen;
        end
      end
    end
  end

  always_comb begin
    slave_if.scmd_accept  = master_if.scmd_accept;
    master_if.mcmd_valid  = slave_if.mcmd_valid;
    master_if.put_command(slave_if.get_command());

    if ((mdata_count == '1) || slave_if.mdata_last) begin
      master_if.mdata_valid = slave_if.mdata_valid;
      slave_if.sdata_accept = master_if.sdata_accept;
    end
    else begin
      master_if.mdata_valid = '0;
      slave_if.sdata_accept = '1;
    end
    master_if.mdata         = mdata;
    master_if.mdata_byteen  = mdata_byteen;
    master_if.mdata_last    = slave_if.mdata_last;
  end
endmodule
