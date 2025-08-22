//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_downsizer_request_path
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  SLAVE_CONFIG          = '0,
  parameter pzcorebus_config  MASTER_CONFIG         = '0,
  parameter int               CONVERSION_RATIO      = 2,
  parameter bit               ALLIGNED_ACCESS_ONLY  = 0
)(
  input var                   i_clk,
  input var                   i_rst_n,
  pzcorebus_if.request_slave  slave_if,
  pzcorebus_if.request_master master_if
);
  typedef logic [MASTER_CONFIG.data_width-1:0]                pzcorebus_data;
  typedef logic [get_byte_enable_width(MASTER_CONFIG, 1)-1:0] pzcorebus_byte_enable;

  localparam  int DATA_SIZE           = MASTER_CONFIG.data_width / MASTER_CONFIG.unit_data_width;
  localparam  int MASTER_BYTE_LSB     = $clog2(MASTER_CONFIG.data_width) - 3;
  localparam  int UNIT_BYTE_LSB       = $clog2(MASTER_CONFIG.unit_data_width) - 3;
  localparam  int LENGTH_WIDTH        = get_unpacked_length_width(SLAVE_CONFIG);
  localparam  int OFFSET_WIDTH        = (DATA_SIZE > 1) ? $clog2(DATA_SIZE) : 1;
  localparam  int DATA_COUNTER_WIDTH  = $clog2(CONVERSION_RATIO);

  logic [LENGTH_WIDTH-1:0]        length;
  logic [LENGTH_WIDTH-1:0]        length_latched;
  logic [OFFSET_WIDTH-1:0]        offset;
  logic [DATA_COUNTER_WIDTH-1:0]  mdata_count;
  logic [DATA_COUNTER_WIDTH-1:0]  mdata_count_latched;
  logic                           mdata_busy;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      mdata_busy  <= '0;
    end
    else if (slave_if.write_data_last_ack()) begin
      mdata_busy  <= '0;
    end
    else if (master_if.write_data_ack()) begin
      mdata_busy  <= '1;
    end
  end

  always_comb begin
    if (slave_if.mcmd_valid && (!mdata_busy)) begin
      length      = get_initial_length(slave_if.mcmd, slave_if.maddr, slave_if.get_length());
      mdata_count = get_initial_data_count(slave_if.mcmd, slave_if.maddr);
    end
    else begin
      length      = length_latched;
      mdata_count = mdata_count_latched;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      length_latched      <= '0;
      mdata_count_latched <= '0;
    end
    else if (master_if.write_data_ack()) begin
      length_latched      <= length      - LENGTH_WIDTH'(DATA_SIZE);
      mdata_count_latched <= mdata_count + DATA_COUNTER_WIDTH'(1);
    end
    else if (slave_if.command_with_data_ack()) begin
      length_latched      <= length;
      mdata_count_latched <= mdata_count;
    end
  end

  function automatic logic [DATA_COUNTER_WIDTH-1:0] get_initial_data_count(
    pzcorebus_command_type                  mcmd,
    logic [SLAVE_CONFIG.address_width-1:0]  maddr
  );
    logic no_offset;

    no_offset = pzcorebus_command_kind'(mcmd) inside {PZCOREBUS_ATOMIC_COMMAND, PZCOREBUS_MESSAGE_COMMAND};
    if (ALLIGNED_ACCESS_ONLY || no_offset) begin
      return DATA_COUNTER_WIDTH'(0);
    end
    else begin
      return maddr[MASTER_BYTE_LSB+:DATA_COUNTER_WIDTH];
    end
  endfunction

  function automatic logic [LENGTH_WIDTH-1:0] get_initial_length(
    pzcorebus_command_type                  mcmd,
    logic [SLAVE_CONFIG.address_width-1:0]  maddr,
    logic [LENGTH_WIDTH-1:0]                length
  );
    logic [LENGTH_WIDTH-1:0]  offset;
    logic                     no_offset;

    no_offset = pzcorebus_command_kind'(mcmd) inside {PZCOREBUS_ATOMIC_COMMAND, PZCOREBUS_MESSAGE_COMMAND};
    if (ALLIGNED_ACCESS_ONLY || (DATA_SIZE == 1) || no_offset) begin
      offset  = LENGTH_WIDTH'(0);
    end
    else begin
      offset  = LENGTH_WIDTH'(maddr[UNIT_BYTE_LSB+:OFFSET_WIDTH]);
    end

    return length + offset;
  endfunction

  always_comb begin
    slave_if.scmd_accept  = master_if.scmd_accept;
    master_if.mcmd_valid  = slave_if.mcmd_valid;
    master_if.put_command(slave_if.get_command());

    if (is_slave_active(length, mdata_count)) begin
      slave_if.sdata_accept = master_if.sdata_accept;
      master_if.mdata_valid = slave_if.mdata_valid;
      master_if.mdata_last  = slave_if.mdata_last;
    end
    else begin
      slave_if.sdata_accept = '0;
      master_if.mdata_valid = slave_if.mdata_valid;
      master_if.mdata_last  = '0;
    end
    master_if.mdata         = get_mdata(slave_if.mdata, mdata_count);
    master_if.mdata_byteen  = get_mdata_byteen(slave_if.mdata_byteen, mdata_count);
  end

  function automatic pzcorebus_data get_mdata(
    pzcorebus_data  [CONVERSION_RATIO-1:0]  mdata,
    logic [DATA_COUNTER_WIDTH-1:0]          mdata_count
  );
    return mdata[mdata_count];
  endfunction

  function automatic pzcorebus_byte_enable get_mdata_byteen(
    pzcorebus_byte_enable [CONVERSION_RATIO-1:0]  mdata_byteen,
    logic [DATA_COUNTER_WIDTH-1:0]                mdata_count
  );
    return mdata_byteen[mdata_count];
  endfunction

  function automatic logic is_slave_active(
    logic [LENGTH_WIDTH-1:0]        length,
    logic [DATA_COUNTER_WIDTH-1:0]  mdata_count
  );
    if (length <= LENGTH_WIDTH'(DATA_SIZE)) begin
      return '1;
    end
    else if (mdata_count == '1) begin
      return '1;
    end
    else begin
      return '0;
    end
  endfunction
endmodule
