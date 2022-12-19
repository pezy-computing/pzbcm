//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
package pzaxi_pkg;
  typedef struct packed {
    shortint  id_width;
    shortint  address_width;
    shortint  data_width;
    shortint  user_request_width;
    shortint  user_data_width;
    shortint  user_response_width;
  } pzaxi_config;

  typedef logic [7:0] pzaxi_burst_length;
  typedef logic [8:0] pzaxi_burst_length_unpacked;

  typedef enum logic [2:0] {
    PZAXI_1_BYTE_BURST    = 3'b000,
    PZAXI_2_BYTES_BURST   = 3'b001,
    PZAXI_4_BYTES_BURST   = 3'b010,
    PZAXI_8_BYTES_BURST   = 3'b011,
    PZAXI_16_BYTES_BURST  = 3'b100,
    PZAXI_32_BYTES_BURST  = 3'b101,
    PZAXI_64_BYTES_BURST  = 3'b110,
    PZAXI_128_BYTES_BURST = 3'b111
  } pzaxi_burst_size;

  typedef enum logic [1:0] {
    PZAXI_FIXED_BURST = 2'b00,
    PZAXI_INCR_BURST  = 2'b01,
    PZAXI_WRAP_BURST  = 2'b10
  } pzaxi_burst_type;

  typedef struct packed {
    logic allocate;
    logic other_allocate;
    logic modifiable;
    logic bufferable;
  } pzaxi_write_cache;

  typedef struct packed {
    logic other_allocate;
    logic allocate;
    logic modifiable;
    logic bufferable;
  } pzaxi_read_cache;

  typedef struct packed {
    logic instruction_access;
    logic non_secure_access;
    logic privileged_access;
  } pzaxi_permission;

  typedef enum logic {
    PZAXI_NORMAL_ACCESS     = 1'b0,
    PAAXI_EXCLUSIVE_ACCESS  = 1'b1
  } pzaxi_lock;

  typedef logic [3:0] pzaxi_qos;

  typedef enum logic [1:0] {
    PZAXI_OKAY    = 2'b00,
    PZAXI_EXOKAY  = 2'b01,
    PZAXI_SLVERR  = 2'b10,
    PZAXI_DECERR  = 2'b11
  } pzaxi_response_status;

  function automatic int clip_width(int width, bit signal_width);
    if ((width <= 0) && signal_width) begin
      return 1;
    end
    else begin
      return width;
    end
  endfunction

  function automatic int get_awuser_width(pzaxi_config bus_config, bit signal_width);
    return clip_width(bus_config.user_request_width, signal_width);
  endfunction

  function automatic int get_wuser_width(pzaxi_config bus_config, bit signal_width);
    return clip_width(bus_config.user_data_width, signal_width);
  endfunction

  function automatic int get_buser_width(pzaxi_config bus_config, bit signal_width);
    return clip_width(bus_config.user_response_width, signal_width);
  endfunction

  function automatic int get_aruser_width(pzaxi_config bus_config, bit signal_width);
    return clip_width(bus_config.user_request_width, signal_width);
  endfunction

  function automatic int get_ruser_width(pzaxi_config bus_config, bit signal_width);
    return clip_width(bus_config.user_response_width + bus_config.user_data_width, signal_width);
  endfunction

  function automatic pzaxi_burst_length_unpacked decode_burst_length(pzaxi_burst_length burst_length);
    return pzaxi_burst_length_unpacked'(burst_length) + pzaxi_burst_length_unpacked'(1);
  endfunction

  function automatic pzaxi_burst_length encode_burst_length(pzaxi_burst_length_unpacked burst_length);
    return pzaxi_burst_length'(burst_length - pzaxi_burst_length_unpacked'(1));
  endfunction
endpackage
