//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
`ifndef PZCOREBUS_MAX_ID_WIDTH
  `define PZCOREBUS_MAX_ID_WIDTH  19
`endif

`ifndef PZCOREBUS_MAX_ADDRESS_WIDTH
  `define PZCOREBUS_MAX_ADDRESS_WIDTH 64
`endif

`ifndef PZCOREBUS_MAX_DATA_WIDTH
  `define PZCOREBUS_MAX_DATA_WIDTH  1024
`endif

`ifndef PZCOREBUS_MIN_DATA_WIDTH
  `define PZCOREBUS_MIN_DATA_WIDTH  32
`endif

`ifndef PZCOREBUS_MAX_BYTE_ENABLE_WIDTH
  `define PZCOREBUS_MAX_BYTE_ENABLE_WIDTH \
  (`PZCOREBUS_MAX_DATA_WIDTH / 8)
`endif

`ifndef PZCOREBUS_MAX_UNIT_ENABLE_WIDTH
  `define PZCOREBUS_MAX_UNIT_ENABLE_WIDTH \
  (`PZCOREBUS_MAX_DATA_WIDTH / `PZCOREBUS_MIN_DATA_WIDTH)
`endif

`ifndef PZCOREBUS_MAX_LENGTH
  `define PZCOREBUS_MAX_LENGTH  1024
`endif

`ifndef PZCOREBUS_MAX_LENGTH_WIDTH
  `define PZCOREBUS_MAX_LENGTH_WIDTH \
  ((`PZCOREBUS_MAX_LENGTH == 1) ? 1 : myclog2(`PZCOREBUS_MAX_LENGTH))
`endif

`ifndef PZCOREBUS_MAX_REQUEST_INFO_WIDTH
  `define PZCOREBUS_MAX_REQUEST_INFO_WIDTH  32
`endif

`ifndef PZCOREBUS_MAX_RESPONSE_INFO_WIDTH
  `define PZCOREBUS_MAX_RESPONSE_INFO_WIDTH 32
`endif

package pzcorebus_pkg;
//--------------------------------------------------------------
//  Typedef
//--------------------------------------------------------------
  typedef enum bit [1:0] {
    PZCOREBUS_CSR,
    PZCOREBUS_MEMORY_L,
    PZCOREBUS_MEMORY_H
  } pzcorebus_profile;

  //  [3]   1: width data
  //        0: without data
  //  [2]   1: need response
  //        0: need no response
  //  [1:0] 0: Normal access
  //        1: Broadcast (for CSR)
  //        2: Atomic
  //        3: Message
  typedef enum logic [3:0] {
    PZCOREBUS_NULL_COMMAND        = 4'b00_00,
    PZCOREBUS_READ                = 4'b01_00,
    PZCOREBUS_WRITE               = 4'b10_00,
    PZCOREBUS_WRITE_NON_POSTED    = 4'b11_00,
    PZCOREBUS_BROADCAST           = 4'b10_01,
    PZCOREBUS_ATOMIC              = 4'b10_10,
    PZCOREBUS_ATOMIC_NON_POSTED   = 4'b11_10,
    PZCOREBUS_MESSAGE             = 4'b00_11,
    PZCOREBUS_MESSAGE_NON_POSTED  = 4'b01_11
  } pzcorebus_command_type;

  localparam  int PZCOREBUS_WITH_DATA_BIT       = 3;
  localparam  int PZCOREBUS_NON_POSTED_BIT      = 2;
  localparam  int PZOCREBUS_COMMAND_KIND_BIT    = 0;
  localparam  int PZOCREBUS_COMMAND_KIND_WIDTH  = 2;

  typedef enum logic {
    PZCOREBUS_RESPONSE            = 1'b0,
    PZCOREBUS_RESPONSE_WITH_DATA  = 1'b1
  } pzcorebus_response_type;

  typedef struct packed {
    pzcorebus_command_type                        command;
    logic [`PZCOREBUS_MAX_ID_WIDTH-1:0]           id;
    logic [`PZCOREBUS_MAX_ADDRESS_WIDTH-1:0]      address;
    logic [`PZCOREBUS_MAX_LENGTH_WIDTH-1:0]       length;
    logic [`PZCOREBUS_MAX_REQUEST_INFO_WIDTH-1:0] info;
    logic [`PZCOREBUS_MAX_DATA_WIDTH-1:0]         data;
  } pzcorebus_command;

  typedef struct packed {
    logic [`PZCOREBUS_MAX_DATA_WIDTH-1:0]         data;
    logic [`PZCOREBUS_MAX_BYTE_ENABLE_WIDTH-1:0]  byte_enable;
    logic                                         last;
  } pzcorebus_write_data;

  typedef struct packed {
    pzcorebus_command     command;
    pzcorebus_write_data  write_data;
  } pzcorebus_request;

  typedef struct packed {
    pzcorebus_response_type                         response;
    logic [`PZCOREBUS_MAX_ID_WIDTH-1:0]             id;
    logic                                           error;
    logic [`PZCOREBUS_MAX_DATA_WIDTH-1:0]           data;
    logic [`PZCOREBUS_MAX_RESPONSE_INFO_WIDTH-1:0]  info;
    logic [`PZCOREBUS_MAX_UNIT_ENABLE_WIDTH-1:0]    unit_enable;
    logic [1:0]                                     last;
  } pzcorebus_response;

//--------------------------------------------------------------
//  Configuration
//--------------------------------------------------------------
  typedef struct packed {
    pzcorebus_profile profile;
    shortint          id_width;
    shortint          address_width;
    shortint          data_width;
    shortint          max_length;
    shortint          request_info_width;
    shortint          response_info_width;
    shortint          unit_data_width;
    shortint          max_data_width;
  } pzcorebus_config;

  localparam  pzcorebus_config  DEFAULT_CONFIG  = '0;

  function automatic int myclog2(bit [31:0] n);
    int result;

    result  = 0;
    for (int i = 31;i >= 0;--i) begin
      if (n[i]) begin
        result  = i;
        break;
      end
    end

    if ((2**result) == n) begin
      return result;
    end
    else begin
      return result + 1;
    end
  endfunction

  function automatic int get_unit_data_width(pzcorebus_config bus_config);
    if (bus_config.profile == PZCOREBUS_MEMORY_H) begin
      return bus_config.unit_data_width;
    end
    else begin
      return bus_config.data_width;
    end
  endfunction

  function automatic int get_data_size(pzcorebus_config bus_config);
    int unit_data_width;
    unit_data_width = get_unit_data_width(bus_config);
    return bus_config.data_width / unit_data_width;
  endfunction

  function automatic int get_max_burst_length(pzcorebus_config bus_config);
    if (bus_config.profile == PZCOREBUS_MEMORY_H) begin
      return bus_config.max_length / (bus_config.data_width / bus_config.unit_data_width);
    end
    else if (bus_config.profile == PZCOREBUS_MEMORY_L) begin
      return bus_config.max_length;
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_length_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    if (bus_config.profile == PZCOREBUS_CSR) begin
      return (typedef_width) ? 1 : 0;
    end
    else if (bus_config.max_length == 1) begin
      return 1;
    end
    else begin
      return myclog2(bus_config.max_length);
    end
  endfunction

  function automatic int get_unpacked_length_width(
    pzcorebus_config  bus_config
  );
    if (bus_config.profile == PZCOREBUS_CSR) begin
      return 1;
    end
    else begin
      return myclog2(bus_config.max_length + 1);
    end
  endfunction

  function automatic int get_burst_length_width(
    pzcorebus_config  bus_config
  );
    if (bus_config.profile == PZCOREBUS_MEMORY_H) begin
      int max_burst;
      max_burst = get_max_burst_length(bus_config);
      return myclog2(max_burst + 1);
    end
    else begin
      return get_unpacked_length_width(bus_config);
    end
  endfunction

  function automatic int get_request_info_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    if (typedef_width && (bus_config.request_info_width == 0)) begin
      return 1;
    end
    else begin
      return bus_config.request_info_width;
    end
  endfunction

  function automatic int get_byte_enable_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    if (bus_config.profile == PZCOREBUS_CSR) begin
      return (typedef_width) ? 1 : 0;
    end
    else begin
      return bus_config.data_width / 8;
    end
  endfunction

  function automatic int get_unit_enable_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    if (bus_config.profile == PZCOREBUS_MEMORY_H) begin
      return bus_config.max_data_width / bus_config.unit_data_width;
    end
    else begin
      return (typedef_width) ? 1 : 0;
    end
  endfunction

  function automatic int get_response_info_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    if (typedef_width && (bus_config.response_info_width == 0)) begin
      return 1;
    end
    else begin
      return bus_config.response_info_width;
    end
  endfunction

  function automatic int get_response_last_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    if (bus_config.profile == PZCOREBUS_MEMORY_H) begin
      return 2;
    end
    else if (bus_config.profile == PZCOREBUS_MEMORY_L) begin
      return 1;
    end
    else begin
      return (typedef_width) ? 1 : 0;
    end
  endfunction

  function automatic int get_response_size_width(
    pzcorebus_config  bus_config
  );
    if (bus_config.profile != PZCOREBUS_MEMORY_H) begin
      return 1;
    end
    else if (bus_config.data_width == bus_config.unit_data_width) begin
      return 1;
    end
    else begin
      int data_size;
      data_size = bus_config.data_width / bus_config.unit_data_width;
      return myclog2(data_size + 1);
    end
  endfunction

  function automatic int get_response_offset_lsb(pzcorebus_config  bus_config);
    if (bus_config.profile == PZCOREBUS_MEMORY_H) begin
      return myclog2(bus_config.unit_data_width / 8);
    end
    else begin
      return 0;
    end
  endfunction

  function automatic int get_response_offset_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    if (bus_config.profile != PZCOREBUS_MEMORY_H) begin
      return (typedef_width) ? 1 : 0;
    end
    else if (bus_config.max_data_width == bus_config.unit_data_width) begin
      return (typedef_width) ? 1 : 0;
    end
    else begin
      return myclog2(bus_config.max_data_width / bus_config.unit_data_width);
    end
  endfunction

  function automatic int get_packed_command_width(pzcorebus_config bus_config);
    int width = 0;

    //  mcmd
    width += $bits(pzcorebus_command_type);
    //  mid
    width += bus_config.id_width;
    //  maddr
    width += bus_config.address_width;
    //  mlength
    width += get_length_width(bus_config, 0);
    //  minfo
    width += get_request_info_width(bus_config, 0);
    //  mdata
    width += (bus_config.profile == PZCOREBUS_CSR) ? bus_config.data_width : 0;

    return width;
  endfunction

  function automatic int get_packed_write_data_width(pzcorebus_config bus_config, bit typedef_width);
    if (bus_config.profile == PZCOREBUS_CSR) begin
      return (typedef_width) ? 1 : 0;
    end
    else begin
      int width = 0;

      //  mdata
      width += bus_config.data_width;
      //  mdata_byteen
      width += get_byte_enable_width(bus_config, typedef_width);
      //  mdata_last
      width += 1;

      return width;
    end
  endfunction

  function automatic int get_packed_response_width(pzcorebus_config bus_config);
    int width = 0;

    //  sresp
    width += $bits(pzcorebus_response_type);
    //  sid
    width += bus_config.id_width;
    //  serror
    width += 1;
    //  sdata
    width += bus_config.data_width;
    //  sinfo
    width += get_response_info_width(bus_config, 0);
    //  sresp_uniten
    width += get_unit_enable_width(bus_config, 0);
    //  sresp_last
    width += get_response_last_width(bus_config, 0);

    return width;
  endfunction
endpackage
