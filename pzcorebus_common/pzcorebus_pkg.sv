//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
`ifndef PZCOREBUS_MAX_ID_WIDTH
  `define PZCOREBUS_MAX_ID_WIDTH  20
`endif

`ifndef PZCOREBUS_MAX_ADDRESS_WIDTH
  `define PZCOREBUS_MAX_ADDRESS_WIDTH 64
`endif

`ifndef PZCOREBUS_MAX_DATA_WIDTH
  `define PZCOREBUS_MAX_DATA_WIDTH  512
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
  ((`PZCOREBUS_MAX_LENGTH == 1) ? 1 : $clog2(`PZCOREBUS_MAX_LENGTH))
`endif

`ifndef PZCOREBUS_MAX_ATOMIC_COMMAND_WIDTH
  `define PZCOREBUS_MAX_ATOMIC_COMMAND_WIDTH  8
`endif

`ifndef PZCOREBUS_MAX_MESSAGE_CODE_WIDTH
  `define PZCOREBUS_MAX_MESSAGE_CODE_WIDTH  1
`endif

`ifndef PZCOREBUS_MAX_REQUEST_PARAM_WIDTH
  `define PZCOREBUS_MAX_REQUEST_PARAM_WIDTH \
  ((`PZCOREBUS_MAX_ATOMIC_COMMAND_WIDTH > `PZCOREBUS_MAX_MESSAGE_CODE_WIDTH) ? \
    `PZCOREBUS_MAX_ATOMIC_COMMAND_WIDTH : `PZCOREBUS_MAX_MESSAGE_CODE_WIDTH)
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

  typedef enum logic [2:0] {
    PZCOREBUS_READ_COMMAND        = 3'b001,
    PZCOREBUS_WRITE_COMMAND       = 3'b100,
    PZCOREBUS_FULL_WRITE_COMMAND  = 3'b101,
    PZCOREBUS_BROADCAST_COMMAND   = 3'b110,
    PZCOREBUS_ATOMIC_COMMAND      = 3'b111,
    PZCOREBUS_MESSAGE_COMMAND     = 3'b010
  } pzcorebus_command_kind;

  //  [3]   1: non-posted request
  //        0: posted request
  //  [2:0] see pzcorebus_command_kind
  typedef enum logic [3:0] {
    PZCOREBUS_NULL_COMMAND          = 4'b0_000,
    PZCOREBUS_READ                  = {1'b1, PZCOREBUS_READ_COMMAND      },
    PZCOREBUS_WRITE                 = {1'b0, PZCOREBUS_WRITE_COMMAND     },
    PZCOREBUS_WRITE_NON_POSTED      = {1'b1, PZCOREBUS_WRITE_COMMAND     },
    PZCOREBUS_FULL_WRITE            = {1'b0, PZCOREBUS_FULL_WRITE_COMMAND},
    PZCOREBUS_FULL_WRITE_NON_POSTED = {1'b1, PZCOREBUS_FULL_WRITE_COMMAND},
    PZCOREBUS_BROADCAST             = {1'b0, PZCOREBUS_BROADCAST_COMMAND },
    PZCOREBUS_BROADCAST_NON_POSTED  = {1'b1, PZCOREBUS_BROADCAST_COMMAND },
    PZCOREBUS_ATOMIC                = {1'b0, PZCOREBUS_ATOMIC_COMMAND    },
    PZCOREBUS_ATOMIC_NON_POSTED     = {1'b1, PZCOREBUS_ATOMIC_COMMAND    },
    PZCOREBUS_MESSAGE               = {1'b0, PZCOREBUS_MESSAGE_COMMAND   },
    PZCOREBUS_MESSAGE_NON_POSTED    = {1'b1, PZCOREBUS_MESSAGE_COMMAND   }
  } pzcorebus_command_type;

  localparam  int PZOCREBUS_COMMAND_KIND_WIDTH  = $bits(pzcorebus_command_kind);
  localparam  int PZOCREBUS_COMMAND_KIND_BIT    = 0;
  localparam  int PZCOREBUS_WITH_DATA_BIT       = PZOCREBUS_COMMAND_KIND_WIDTH - 1;
  localparam  int PZCOREBUS_NON_POSTED_BIT      = PZCOREBUS_WITH_DATA_BIT + 1;

  typedef enum logic {
    PZCOREBUS_RESPONSE            = 1'b0,
    PZCOREBUS_RESPONSE_WITH_DATA  = 1'b1
  } pzcorebus_response_type;

  typedef struct packed {
    pzcorebus_command_type                          command;
    logic [`PZCOREBUS_MAX_ID_WIDTH-1:0]             id;
    logic [`PZCOREBUS_MAX_ADDRESS_WIDTH-1:0]        address;
    logic [`PZCOREBUS_MAX_LENGTH_WIDTH-1:0]         length;
    logic [`PZCOREBUS_MAX_REQUEST_PARAM_WIDTH-1:0]  param;
    logic [`PZCOREBUS_MAX_REQUEST_INFO_WIDTH-1:0]   info;
    logic [`PZCOREBUS_MAX_DATA_WIDTH-1:0]           data;
    logic [`PZCOREBUS_MAX_BYTE_ENABLE_WIDTH-1:0]    byte_enable;
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
  localparam  bit PZCOREBUS_ENABLE_DEBUG  =
    `ifndef SYNTHESIS 1
    `else             0 `endif;

  localparam  bit PZCOREBUS_ENABLE_SVA_CHECKER  =
    PZCOREBUS_ENABLE_DEBUG  &&
    `ifndef PZCOREBUS_DISABLE_SVA_CHECKER 1
    `else                                 0 `endif;

  typedef struct packed {
    shortint  lsb;
    shortint  width;
  } pzcorebus_signal_info;

  typedef struct packed {
    pzcorebus_signal_info mcmd;
    pzcorebus_signal_info mid;
    pzcorebus_signal_info maddr;
    pzcorebus_signal_info mlength;
    pzcorebus_signal_info mparam;
    pzcorebus_signal_info minfo;
    pzcorebus_signal_info mdata;
    pzcorebus_signal_info mdata_byteen;
    shortint              mlength_unpacked_width;
    shortint              mburst_length_width;
    shortint              mcmd_packed_width;
  } pzcorebus_mcmd_info;

  typedef struct packed {
    pzcorebus_signal_info mdata;
    pzcorebus_signal_info mdata_byteen;
    pzcorebus_signal_info mdata_last;
    shortint              mdata_packed_width;
  } pzcorebus_mdata_info;

  typedef struct packed {
    pzcorebus_signal_info sresp;
    pzcorebus_signal_info sid;
    pzcorebus_signal_info serror;
    pzcorebus_signal_info sdata;
    pzcorebus_signal_info sinfo;
    pzcorebus_signal_info sresp_uniten;
    pzcorebus_signal_info sresp_last;
    shortint              sresp_packed_width;
  } pzcorebus_sresp_info;

  typedef struct packed {
    pzcorebus_profile     profile;
    shortint              id_width;
    shortint              address_width;
    shortint              data_width;
    shortint              unit_data_width;
    shortint              max_data_width;
    shortint              data_size;
    bit                   use_byte_enable;
    shortint              byte_enable_width;
    shortint              max_length;
    shortint              max_burst_length;
    shortint              atomic_command_width;
    shortint              message_code_width;
    shortint              request_info_width;
    shortint              response_info_width;
    shortint              response_boundary;
    pzcorebus_mcmd_info   mcmd_info;
    pzcorebus_mdata_info  mdata_info;
    pzcorebus_sresp_info  sresp_info;
  } pzcorebus_config;

  function automatic shortint __calc_next_lsb(pzcorebus_signal_info info);
    return info.lsb + info.width;
  endfunction

  function automatic pzcorebus_config create_corebus_config(
    pzcorebus_profile profile,
    shortint          id_width,
    shortint          address_width,
    shortint          data_width,
    bit               use_byte_enable,
    shortint          max_length,
    shortint          atomic_command_width,
    shortint          message_code_width,
    shortint          request_info_width,
    shortint          response_info_width,
    shortint          unit_data_width,
    shortint          max_data_width,
    shortint          response_boundary
  );
    bit                   is_csr;
    bit                   is_memory_h;
    pzcorebus_config      bus_config;
    pzcorebus_mcmd_info   mcmd_info;
    pzcorebus_mdata_info  mdata_info;
    pzcorebus_sresp_info  sresp_info;

    is_csr      = profile == PZCOREBUS_CSR;
    is_memory_h = profile == PZCOREBUS_MEMORY_H;

    bus_config.profile              = profile;
    bus_config.id_width             = id_width;
    bus_config.address_width        = address_width;
    bus_config.data_width           = data_width;
    bus_config.unit_data_width      = (is_csr) ? data_width : unit_data_width;
    bus_config.max_data_width       = (is_memory_h) ? max_data_width : data_width;
    bus_config.data_size            = bus_config.data_width / bus_config.unit_data_width;
    bus_config.use_byte_enable      = use_byte_enable;
    bus_config.byte_enable_width    = (use_byte_enable) ? data_width / 8 : 0;
    bus_config.max_length           = (is_csr) ? 1 : max_length;
    bus_config.max_burst_length     = (is_csr) ? 1 : bus_config.max_length / bus_config.data_size;
    bus_config.atomic_command_width = (is_csr) ? 0 : atomic_command_width;
    bus_config.message_code_width   = (is_csr) ? 0 : message_code_width;
    bus_config.request_info_width   = request_info_width;
    bus_config.response_info_width  = response_info_width;
    bus_config.response_boundary    = response_boundary;

    //  mcmd info
    mcmd_info.mcmd.lsb      = 0;
    mcmd_info.mcmd.width    = $bits(pzcorebus_command_type);
    mcmd_info.mid.lsb       = __calc_next_lsb(mcmd_info.mcmd);
    mcmd_info.mid.width     = bus_config.id_width;
    mcmd_info.maddr.lsb     = __calc_next_lsb(mcmd_info.mid);
    mcmd_info.maddr.width   = bus_config.address_width;
    mcmd_info.mlength.lsb   = __calc_next_lsb(mcmd_info.maddr);
    mcmd_info.mlength.width = (bus_config.max_length == 0) ? 0
                            : (bus_config.max_length == 1) ? 1
                            : $clog2(bus_config.max_length);
    mcmd_info.mparam.lsb    = __calc_next_lsb(mcmd_info.mlength);
    mcmd_info.mparam.width  = (bus_config.atomic_command_width > bus_config.message_code_width)
                                ? bus_config.atomic_command_width
                                : bus_config.message_code_width;
    mcmd_info.minfo.lsb     = __calc_next_lsb(mcmd_info.mparam);
    mcmd_info.minfo.width   = bus_config.request_info_width;
    if (is_csr) begin
      mcmd_info.mdata.lsb           = __calc_next_lsb(mcmd_info.minfo);
      mcmd_info.mdata.width         = bus_config.data_width;
      mcmd_info.mdata_byteen.lsb    = __calc_next_lsb(mcmd_info.mdata);
      mcmd_info.mdata_byteen.width  = bus_config.byte_enable_width;
    end
    else begin
      mcmd_info.mdata.lsb           = __calc_next_lsb(mcmd_info.minfo);
      mcmd_info.mdata.width         = 0;
      mcmd_info.mdata_byteen.lsb    = __calc_next_lsb(mcmd_info.mdata);
      mcmd_info.mdata_byteen.width  = 0;
    end
    mcmd_info.mlength_unpacked_width  = (is_csr) ? 0 : $clog2(bus_config.max_length + 1);
    mcmd_info.mburst_length_width     = (is_csr) ? 0 : $clog2(bus_config.max_burst_length + 1);
    mcmd_info.mcmd_packed_width       = mcmd_info.mcmd.width
                                      + mcmd_info.mid.width
                                      + mcmd_info.maddr.width
                                      + mcmd_info.mlength.width
                                      + mcmd_info.mparam.width
                                      + mcmd_info.minfo.width
                                      + mcmd_info.mdata.width
                                      + mcmd_info.mdata_byteen.width;

    //  mdata info
    if (!is_csr) begin
      mdata_info.mdata_last.lsb     = 0;
      mdata_info.mdata_last.width   = 1;
      mdata_info.mdata.lsb          = __calc_next_lsb(mdata_info.mdata_last);
      mdata_info.mdata.width        = bus_config.data_width;
      mdata_info.mdata_byteen.lsb   = __calc_next_lsb(mdata_info.mdata);
      mdata_info.mdata_byteen.width = bus_config.byte_enable_width;
      mdata_info.mdata_packed_width = mdata_info.mdata_last.width
                                    + mdata_info.mdata.width
                                    + mdata_info.mdata_byteen.width;
    end
    else begin
      mdata_info  = pzcorebus_mdata_info'(0);
    end

    //  sresp info
    sresp_info.sresp.lsb          = 0;
    sresp_info.sresp.width        = $bits(pzcorebus_response_type);
    sresp_info.sid.lsb            = __calc_next_lsb(sresp_info.sresp);
    sresp_info.sid.width          = bus_config.id_width;
    sresp_info.serror.lsb         = __calc_next_lsb(sresp_info.sid);
    sresp_info.serror.width       = 1;
    sresp_info.sdata.lsb          = __calc_next_lsb(sresp_info.serror);
    sresp_info.sdata.width        = bus_config.data_width;
    sresp_info.sinfo.lsb          = __calc_next_lsb(sresp_info.sdata);
    sresp_info.sinfo.width        = bus_config.response_info_width;
    sresp_info.sresp_uniten.lsb   = __calc_next_lsb(sresp_info.sinfo);
    sresp_info.sresp_uniten.width = (is_memory_h)
                                      ? bus_config.max_data_width / bus_config.unit_data_width
                                      : 0;
    sresp_info.sresp_last.lsb     = __calc_next_lsb(sresp_info.sresp_uniten);
    sresp_info.sresp_last.width   = (is_csr     ) ? 0
                                  : (is_memory_h) ? 2
                                  : 1;
    sresp_info.sresp_packed_width = sresp_info.sresp.width
                                  + sresp_info.sid.width
                                  + sresp_info.serror.width
                                  + sresp_info.sdata.width
                                  + sresp_info.sinfo.width
                                  + sresp_info.sresp_uniten.width
                                  + sresp_info.sresp_last.width;


    bus_config.mcmd_info  = mcmd_info;
    bus_config.mdata_info = mdata_info;
    bus_config.sresp_info = sresp_info;
    return bus_config;
  endfunction

  localparam  pzcorebus_config  DEFAULT_CONFIG  = '0;

  function automatic bit is_csr_profile(pzcorebus_config bus_config);
    return bus_config.profile == PZCOREBUS_CSR;
  endfunction

  function automatic bit is_memory_h_profile(pzcorebus_config bus_config);
    return bus_config.profile == PZCOREBUS_MEMORY_H;
  endfunction

  function automatic bit is_memory_l_profile(pzcorebus_config bus_config);
    return bus_config.profile == PZCOREBUS_MEMORY_L;
  endfunction

  function automatic bit is_memory_profile(pzcorebus_config bus_config);
    return !is_csr_profile(bus_config);
  endfunction

  function automatic shortint get_signal_width(shortint width, bit typedef_width);
    if (typedef_width && (width < 1)) begin
      return 1;
    end
    else begin
      return width;
    end
  endfunction

  function automatic shortint get_length_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    return get_signal_width(bus_config.mcmd_info.mlength.width, typedef_width);
  endfunction

  function automatic shortint get_unpacked_length_width(
    pzcorebus_config  bus_config
  );
    return get_signal_width(bus_config.mcmd_info.mlength_unpacked_width, 1);
  endfunction

  function automatic shortint get_burst_length_width(
    pzcorebus_config  bus_config
  );
    return get_signal_width(bus_config.mcmd_info.mburst_length_width, 1);
  endfunction

  function automatic shortint get_request_param_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    return get_signal_width(bus_config.mcmd_info.mparam.width, typedef_width);
  endfunction

  function automatic shortint get_request_info_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    return get_signal_width(bus_config.mcmd_info.minfo.width, typedef_width);
  endfunction

  function automatic shortint get_byte_enable_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    return get_signal_width(bus_config.byte_enable_width, typedef_width);
  endfunction

  function automatic shortint get_unit_enable_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    return get_signal_width(bus_config.sresp_info.sresp_uniten.width, typedef_width);
  endfunction

  function automatic shortint get_response_info_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    return get_signal_width(bus_config.sresp_info.sinfo.width, typedef_width);
  endfunction

  function automatic shortint get_response_last_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    return get_signal_width(bus_config.sresp_info.sresp_last.width, typedef_width);
  endfunction

  function automatic shortint get_response_size_width(
    pzcorebus_config  bus_config
  );
    if (!is_memory_h_profile(bus_config)) begin
      return 1;
    end
    else if (bus_config.data_width == bus_config.unit_data_width) begin
      return 1;
    end
    else begin
      return $clog2(bus_config.data_size + 1);
    end
  endfunction

  function automatic shortint get_response_offset_lsb(pzcorebus_config  bus_config);
    if (is_memory_h_profile(bus_config)) begin
      return $clog2(bus_config.unit_data_width / 8);
    end
    else begin
      return 0;
    end
  endfunction

  function automatic shortint get_response_offset_width(
    pzcorebus_config  bus_config,
    bit               typedef_width
  );
    shortint  width;

    if (is_memory_h_profile(bus_config)) begin
      width = $clog2(bus_config.max_data_width / bus_config.unit_data_width);
    end
    else begin
      width = 0;
    end

    return get_signal_width(width, typedef_width);
  endfunction

  function automatic shortint get_packed_command_width(pzcorebus_config bus_config);
    return get_signal_width(bus_config.mcmd_info.mcmd_packed_width, 1);
  endfunction

  function automatic shortint get_packed_write_data_width(pzcorebus_config bus_config, bit typedef_width);
    return get_signal_width(bus_config.mdata_info.mdata_packed_width, typedef_width);
  endfunction

  function automatic shortint get_packed_response_width(pzcorebus_config bus_config);
    return get_signal_width(bus_config.sresp_info.sresp_packed_width, 1);
  endfunction
endpackage
