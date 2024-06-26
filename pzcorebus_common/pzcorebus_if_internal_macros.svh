//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
`ifndef INCLUDED_PZCOREBUS_INTERNAL_MACROS_SVH
`define INCLUDED_PZCOREBUS_INTERNAL_MACROS_SVH

`define pzcorebus_if_define_types(BUS_CONFIG) \
typedef logic [BUS_CONFIG.id_width-1:0]                         pzcorebus_id; \
typedef logic [BUS_CONFIG.address_width-1:0]                    pzcorebus_addrss; \
typedef logic [get_length_width(BUS_CONFIG, 1)-1:0]             pzcorebus_length; \
typedef logic [get_unpacked_length_width(BUS_CONFIG)-1:0]       pzcorebus_unpacked_length; \
typedef logic [get_burst_length_width(BUS_CONFIG)-1:0]          pzcorebus_burst_length; \
typedef logic [get_request_param_width(BUS_CONFIG, 1)-1:0]      pzcorebus_request_param; \
typedef logic [get_request_info_width(BUS_CONFIG, 1)-1:0]       pzcorebus_request_info; \
typedef logic [get_response_info_width(BUS_CONFIG, 1)-1:0]      pzcorebus_response_info; \
typedef logic [BUS_CONFIG.data_width-1:0]                       pzcorebus_data; \
typedef logic [get_byte_enable_width(BUS_CONFIG, 1)-1:0]        pzcorebus_byte_enable; \
typedef logic [get_unit_enable_width(BUS_CONFIG, 1)-1:0]        pzcorebus_unit_enable; \
typedef logic [get_response_last_width(BUS_CONFIG, 1)-1:0]      pzcorebus_response_last; \
typedef logic [get_packed_command_width(BUS_CONFIG)-1:0]        pzcorebus_packed_command; \
typedef logic [get_packed_write_data_width(BUS_CONFIG, 1)-1:0]  pzcorebus_packed_write_data; \
typedef logic [get_packed_response_width(BUS_CONFIG)-1:0]       pzcorebus_packed_response; \
typedef struct packed { \
  pzcorebus_packed_command    command; \
  pzcorebus_packed_write_data write_data; \
} pzcorebus_packed_request;

`define pzcorebus_if_declare_request_signals \
logic                     scmd_accept; \
logic                     mcmd_valid; \
pzcorebus_command_type    mcmd; \
pzcorebus_id              mid; \
pzcorebus_addrss          maddr; \
pzcorebus_length          mlength; \
pzcorebus_request_param   mparam; \
pzcorebus_request_info    minfo; \
logic                     sdata_accept; \
logic                     mdata_valid; \
pzcorebus_data            mdata; \
pzcorebus_byte_enable     mdata_byteen; \
logic                     mdata_last;

`define pzcorebus_if_declare_response_signals \
logic                     mresp_accept; \
logic                     sresp_valid; \
pzcorebus_response_type   sresp; \
pzcorebus_id              sid; \
logic                     serror; \
pzcorebus_data            sdata; \
pzcorebus_response_info   sinfo; \
pzcorebus_unit_enable     sresp_uniten; \
pzcorebus_response_last   sresp_last;

`define pzcorebus_if_get_packer(packer, info) \
packer[info.lsb+:((info.width>0)?info.width:1)]

`define pzcorebus_if_define_request_api(BUS_CONFIG) \
localparam  shortint  COMMAND_PACKER_WIDTH    = BUS_CONFIG.mcmd_info.mcmd_packed_width + 1; \
localparam  shortint  WRITE_DATA_PACKER_WIDTH = BUS_CONFIG.mdata_info.mdata_packed_width + 1; \
\
function automatic pzcorebus_packed_command get_packed_command(); \
  logic [COMMAND_PACKER_WIDTH-1:0]  packer; \
  `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mcmd)   = mcmd; \
  `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mid)    = mid; \
  `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.maddr)  = maddr; \
  if (BUS_CONFIG.mcmd_info.mlength.width > 0) begin \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mlength)  = mlength; \
  end \
  if (BUS_CONFIG.mcmd_info.mparam.width > 0) begin \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mparam) = mparam; \
  end \
  if (BUS_CONFIG.mcmd_info.minfo.width > 0) begin \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.minfo)  = minfo; \
  end \
  if (BUS_CONFIG.mcmd_info.mdata.width > 0) begin \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mdata)  = mdata; \
  end \
  if (BUS_CONFIG.mcmd_info.mdata_byteen.width > 0) begin \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mdata_byteen) = mdata_byteen; \
  end \
  return pzcorebus_packed_command'(packer); \
endfunction \
\
function automatic void put_packed_command(pzcorebus_packed_command command); \
  logic [COMMAND_PACKER_WIDTH-1:0]  packer; \
  packer  = COMMAND_PACKER_WIDTH'(command); \
  mcmd    = pzcorebus_command_type'(`pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mcmd)); \
  mid     = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mid); \
  maddr   = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.maddr); \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    mlength = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mlength); \
  end \
  else begin \
    mlength = '0; \
  end \
  if (BUS_CONFIG.mcmd_info.mparam.width > 0) begin \
    mparam  = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mparam); \
  end \
  else begin \
    mparam  = '0; \
  end \
  if (BUS_CONFIG.mcmd_info.minfo.width > 0) begin \
    minfo = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.minfo); \
  end \
  else begin \
    minfo = '0; \
  end \
  if (`pzcorebus_csr_profile(BUS_CONFIG)) begin \
    mdata = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mdata); \
    if (BUS_CONFIG.use_byte_enable) begin \
      mdata_byteen  = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mcmd_info.mdata_byteen); \
    end \
    else begin \
      mdata_byteen  = '0; \
    end \
  end \
endfunction \
\
function automatic pzcorebus_command get_command(); \
  pzcorebus_command command; \
  command.command = mcmd; \
  command.id      = mid; \
  command.address = maddr; \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    command.length  = mlength; \
  end \
  else begin \
    command.length  = '0; \
  end \
  if (BUS_CONFIG.mcmd_info.mparam.width > 0) begin \
    command.param = mparam; \
  end \
  else begin \
    command.param = '0; \
  end \
  if (BUS_CONFIG.mcmd_info.minfo.width > 0) begin \
    command.info  = minfo; \
  end \
  else begin \
    command.info  = '0; \
  end \
  if (`pzcorebus_csr_profile(BUS_CONFIG)) begin \
    command.data  = mdata; \
  end \
  else begin \
    command.data  = '0; \
  end \
  if (`pzcorebus_csr_profile(BUS_CONFIG) && BUS_CONFIG.use_byte_enable) begin \
    command.byte_enable = mdata_byteen; \
  end \
  else begin \
    command.byte_enable = '0; \
  end \
  return command; \
endfunction \
\
function automatic void put_command(pzcorebus_command command); \
  mcmd  = command.command; \
  mid   = command.id; \
  maddr = command.address; \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    mlength = command.length; \
  end \
  else begin \
    mlength = '0; \
  end \
  if (BUS_CONFIG.mcmd_info.mparam.width > 0) begin \
    mparam  = command.param; \
  end \
  else begin \
    mparam  = '0; \
  end \
  if (BUS_CONFIG.mcmd_info.minfo.width > 0) begin \
    minfo = command.info; \
  end \
  else begin \
    minfo = '0; \
  end \
  if (`pzcorebus_csr_profile(BUS_CONFIG)) begin \
    mdata = command.data; \
    if (BUS_CONFIG.use_byte_enable) begin \
      mdata_byteen  = command.byte_enable; \
    end \
    else begin \
      mdata_byteen  = '0; \
    end \
  end \
endfunction \
\
function automatic pzcorebus_packed_write_data get_packed_write_data(); \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    logic [WRITE_DATA_PACKER_WIDTH-1:0] packer; \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.mdata_info.mdata_last)  = mdata_last; \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.mdata_info.mdata)       = mdata; \
    if (BUS_CONFIG.use_byte_enable) begin \
      `pzcorebus_if_get_packer(packer, BUS_CONFIG.mdata_info.mdata_byteen)  = mdata_byteen; \
    end \
    return pzcorebus_packed_write_data'(packer); \
  end \
  else begin \
    return '0; \
  end \
endfunction \
\
function automatic void put_packed_write_data(pzcorebus_packed_write_data write_data); \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    logic [WRITE_DATA_PACKER_WIDTH-1:0] packer; \
    packer      = WRITE_DATA_PACKER_WIDTH'(write_data); \
    mdata_last  = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mdata_info.mdata_last); \
    mdata       = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mdata_info.mdata); \
    if (BUS_CONFIG.use_byte_enable) begin \
      mdata_byteen  = `pzcorebus_if_get_packer(packer, BUS_CONFIG.mdata_info.mdata_byteen); \
    end \
    else begin \
      mdata_byteen  = '0; \
    end \
  end \
  else begin \
    mdata_last  = '0; \
  end \
endfunction \
\
function automatic pzcorebus_write_data get_write_data(); \
  pzcorebus_write_data  write_data; \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    write_data.last = mdata_last; \
    write_data.data = mdata; \
    if (BUS_CONFIG.use_byte_enable) begin \
      write_data.byte_enable  = mdata_byteen; \
    end \
    else begin \
      write_data.byte_enable  = '0; \
    end \
  end \
  else begin \
    write_data.last         = '0; \
    write_data.data         = '0; \
    write_data.byte_enable  = '0; \
  end \
  return write_data; \
endfunction \
\
function automatic void put_write_data(pzcorebus_write_data write_data); \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    mdata_last  = write_data.last; \
    mdata       = write_data.data; \
    if (BUS_CONFIG.use_byte_enable) begin \
      mdata_byteen  = write_data.byte_enable; \
    end \
    else begin \
      mdata_byteen  = '0; \
    end \
  end \
  else begin \
    mdata_last  = '0; \
  end \
endfunction \
\
function automatic pzcorebus_packed_request get_packed_request(); \
  pzcorebus_packed_request  request; \
  request.command     = get_packed_command(); \
  request.write_data  = get_packed_write_data(); \
  return request; \
endfunction \
\
function automatic void put_packed_request(pzcorebus_packed_request request); \
  put_packed_command(request.command); \
  put_packed_write_data(request.write_data); \
endfunction \
\
function automatic pzcorebus_request get_request(); \
  pzcorebus_request request; \
  request.command     = get_command(); \
  request.write_data  = get_write_data(); \
  return request; \
endfunction \
\
function automatic void put_request(pzcorebus_request request); \
  put_command(request.command); \
  put_write_data(request.write_data); \
endfunction \
\
function automatic logic is_non_posted_command(); \
  return mcmd[PZCOREBUS_NON_POSTED_BIT] == '1; \
endfunction \
\
function automatic logic is_posted_command(); \
  return mcmd[PZCOREBUS_NON_POSTED_BIT] == '0; \
endfunction \
\
function automatic logic is_command_with_data(); \
  return mcmd[PZCOREBUS_WITH_DATA_BIT] == '1; \
endfunction \
\
function automatic logic is_command_no_data(); \
  return mcmd[PZCOREBUS_WITH_DATA_BIT] == '0; \
endfunction \
\
function automatic logic is_command_with_response_data(); \
  return mcmd inside {PZCOREBUS_READ, PZCOREBUS_ATOMIC_NON_POSTED}; \
endfunction \
\
function automatic pzcorebus_command_kind get_command_kind(); \
  return pzcorebus_command_kind'(mcmd); \
endfunction \
\
function automatic logic is_read_command(); \
  return get_command_kind() == PZCOREBUS_READ_COMMAND; \
endfunction \
\
function automatic logic is_write_command(); \
  return get_command_kind() == PZCOREBUS_WRITE_COMMAND; \
endfunction \
\
function automatic logic is_full_write_command(); \
  return \
    `pzcorebus_memoy_profile(BUS_CONFIG) && \
    (get_command_kind() == PZCOREBUS_FULL_WRITE_COMMAND); \
endfunction \
\
function automatic logic is_broadcast_command(); \
  return \
    `pzcorebus_csr_profile(BUS_CONFIG) && \
    (get_command_kind() == PZCOREBUS_BROADCAST_COMMAND); \
endfunction \
\
function automatic logic is_write_access_command(); \
  return is_write_command() || is_full_write_command() || is_broadcast_command(); \
endfunction \
\
function automatic logic is_posted_write_acess_command(); \
  return is_posted_command() && is_write_access_command(); \
endfunction \
\
function automatic logic is_non_posted_write_access_command(); \
  return is_non_posted_command() && is_write_access_command(); \
endfunction \
\
function automatic logic is_atomic_command(); \
  return \
    `pzcorebus_memoy_profile(BUS_CONFIG) && \
    (get_command_kind() == PZCOREBUS_ATOMIC_COMMAND); \
endfunction\
\
function automatic logic is_message_command(); \
  return \
    `pzcorebus_memoy_profile(BUS_CONFIG) && \
    (get_command_kind() == PZCOREBUS_MESSAGE_COMMAND); \
endfunction \
\
function automatic logic command_ack(); \
  return mcmd_valid && scmd_accept; \
endfunction \
\
function automatic logic command_with_data_ack(); \
  return command_ack() && is_command_with_data(); \
endfunction \
\
function automatic logic command_no_data_ack(); \
  return command_ack() && is_command_no_data(); \
endfunction \
\
function automatic logic command_with_data_valid(); \
  return mcmd_valid && is_command_with_data(); \
endfunction \
\
function automatic logic command_no_data_valid(); \
  return mcmd_valid && is_command_no_data(); \
endfunction \
\
function automatic logic command_posted_ack(); \
  return command_ack() && is_posted_command(); \
endfunction \
\
function automatic logic command_non_posted_ack(); \
  return command_ack() && is_non_posted_command(); \
endfunction \
\
function automatic logic command_posted_valid(); \
  return mcmd_valid && is_posted_command(); \
endfunction \
\
function automatic logic command_non_posted_valid(); \
  return mcmd_valid && is_non_posted_command(); \
endfunction \
\
function automatic logic command_valid(pzcorebus_command_type command); \
  return mcmd_valid && (command == mcmd); \
endfunction \
\
function automatic logic write_data_ack(); \
  return \
    `pzcorebus_memoy_profile(BUS_CONFIG) && \
    (mdata_valid && sdata_accept); \
endfunction \
\
function automatic logic write_data_last_ack(); \
  return write_data_ack() && mdata_last; \
endfunction \
\
function automatic pzcorebus_unpacked_length unpack_length(); \
  if (mlength == '0) begin \
    return pzcorebus_unpacked_length'(BUS_CONFIG.max_length); \
  end \
  else begin \
    return pzcorebus_unpacked_length'(mlength); \
  end \
endfunction \
\
localparam  int LENGTH_OFFSET_LSB   = $clog2(BUS_CONFIG.unit_data_width / 8); \
localparam  int LENGTH_OFFSET_WIDTH = (BUS_CONFIG.data_size > 1) ? $clog2(BUS_CONFIG.data_size) : 1; \
\
function automatic pzcorebus_unpacked_length get_length(); \
  case (1'b1) \
    `pzcorebus_csr_profile(BUS_CONFIG): return pzcorebus_unpacked_length'(1); \
    is_message_command():               return pzcorebus_unpacked_length'(0); \
    default:                            return unpack_length(); \
  endcase \
endfunction \
\
function automatic pzcorebus_unpacked_length get_aligned_length(); \
  pzcorebus_unpacked_length offset; \
  if ((BUS_CONFIG.data_size == 1) || is_atomic_command() || is_message_command()) begin \
    offset  = pzcorebus_unpacked_length'(0); \
  end \
  else begin \
    offset  = pzcorebus_unpacked_length'(maddr[LENGTH_OFFSET_LSB+:LENGTH_OFFSET_WIDTH]); \
  end \
  return get_length() + offset; \
endfunction \
\
function automatic pzcorebus_burst_length get_burst_length(); \
  if ((BUS_CONFIG.data_size == 1) || `pzcorebus_csr_profile(BUS_CONFIG)) begin \
    return pzcorebus_burst_length'(get_length()); \
  end \
  else begin \
    pzcorebus_unpacked_length length; \
    length  = get_aligned_length() + pzcorebus_unpacked_length'(BUS_CONFIG.data_size - 1); \
    return pzcorebus_burst_length'(length / BUS_CONFIG.data_size); \
  end \
endfunction \
\
function automatic pzcorebus_unpacked_length get_response_length(); \
  case (1'b1) \
    is_posted_command():  return pzcorebus_unpacked_length'(0); \
    is_read_command(), \
    is_atomic_command():  return unpack_length(); \
    default:              return pzcorebus_unpacked_length'(BUS_CONFIG.data_size); \
  endcase \
endfunction

`define pzcorebus_if_define_response_api(BUS_CONFIG) \
localparam  shortint  RESPONSE_PACKER_WIDTH = BUS_CONFIG.sresp_info.sresp_packed_width + 1; \
\
function automatic pzcorebus_packed_response get_packed_response(); \
  logic [RESPONSE_PACKER_WIDTH-1:0] packer; \
  `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sresp)   = sresp; \
  `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sid)     = sid; \
  `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.serror)  = serror; \
  `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sdata)   = sdata; \
  if (BUS_CONFIG.sresp_info.sinfo.width > 0) begin \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sinfo) = sinfo; \
  end \
  if (`pzcorebus_memoy_h_profile(BUS_CONFIG)) begin \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sresp_uniten)  = sresp_uniten; \
  end \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sresp_last)  = sresp_last; \
  end \
  return pzcorebus_packed_response'(packer); \
endfunction \
\
function automatic void put_packed_response(pzcorebus_packed_response response); \
  logic [RESPONSE_PACKER_WIDTH-1:0] packer; \
  packer  = RESPONSE_PACKER_WIDTH'(response); \
  sresp   = pzcorebus_response_type'(`pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sresp)); \
  sid     = `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sid); \
  serror  = `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.serror); \
  sdata   = `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sdata); \
  if (BUS_CONFIG.sresp_info.sinfo.width > 0) begin \
    sinfo = `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sinfo); \
  end \
  else begin \
    sinfo = '0; \
  end \
  if (`pzcorebus_memoy_h_profile(BUS_CONFIG)) begin \
    sresp_uniten  = `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sresp_uniten); \
  end \
  else begin \
    sresp_uniten  = '0; \
  end \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    sresp_last  = `pzcorebus_if_get_packer(packer, BUS_CONFIG.sresp_info.sresp_last); \
  end \
  else begin \
    sresp_last  = '0; \
  end \
endfunction \
\
function automatic pzcorebus_response get_response(); \
  pzcorebus_response  response; \
  response.response     = sresp; \
  response.id           = sid; \
  response.error        = serror; \
  response.data         = sdata; \
  response.info         = (BUS_CONFIG.sresp_info.sinfo.width > 0 ) ? sinfo        : '0; \
  response.unit_enable  = (`pzcorebus_memoy_h_profile(BUS_CONFIG)) ? sresp_uniten : '0; \
  response.last         = (`pzcorebus_memoy_profile(BUS_CONFIG)  ) ? sresp_last   : '0; \
  return response; \
endfunction \
\
function automatic void put_response(pzcorebus_response response); \
  sresp   = response.response; \
  sid     = response.id; \
  serror  = response.error; \
  sdata   = response.data; \
  if (BUS_CONFIG.sresp_info.sinfo.width > 0) begin \
    sinfo = response.info; \
  end \
  else begin \
    sinfo = '0; \
  end \
  if (`pzcorebus_memoy_h_profile(BUS_CONFIG)) begin \
    sresp_uniten  = response.unit_enable; \
  end \
  else begin \
    sresp_uniten  = '0; \
  end \
  if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin \
    sresp_last  = response.last; \
  end \
  else begin \
    sresp_last  = '0; \
  end \
endfunction \
\
function automatic logic response_ack(); \
  return sresp_valid && mresp_accept; \
endfunction \
\
function automatic logic response_last_ack(); \
  return response_ack() && (`pzcorebus_csr_profile(BUS_CONFIG) || sresp_last[0]); \
endfunction \
\
function automatic logic response_last_burst_ack(); \
  return response_ack() && (`pzcorebus_csr_profile(BUS_CONFIG) || sresp_last[$bits(pzcorebus_response_last)-1]); \
endfunction \
\
function automatic logic response_with_data_ack(); \
  return response_ack() && (sresp == PZCOREBUS_RESPONSE_WITH_DATA); \
endfunction \
\
function automatic logic response_no_data_ack(); \
  return response_ack() && (sresp == PZCOREBUS_RESPONSE); \
endfunction

`define pzcorebus_if_define_request_modports \
modport request_master ( \
  input   scmd_accept, \
  output  mcmd_valid, \
  output  mcmd, \
  output  mid, \
  output  maddr, \
  output  mlength, \
  output  mparam, \
  output  minfo, \
  input   sdata_accept, \
  output  mdata_valid, \
  output  mdata, \
  output  mdata_byteen, \
  output  mdata_last, \
  import  put_packed_command, \
  import  put_command, \
  import  put_packed_write_data, \
  import  put_write_data, \
  import  put_packed_request, \
  import  put_request, \
  import  is_non_posted_command, \
  import  is_posted_command, \
  import  is_command_with_data, \
  import  is_command_no_data, \
  import  is_command_with_response_data, \
  import  get_command_kind, \
  import  is_read_command, \
  import  is_write_command, \
  import  is_full_write_command, \
  import  is_broadcast_command, \
  import  is_write_access_command, \
  import  is_posted_write_acess_command, \
  import  is_non_posted_write_access_command, \
  import  is_atomic_command, \
  import  is_message_command, \
  import  command_ack, \
  import  command_with_data_ack, \
  import  command_no_data_ack, \
  import  command_with_data_valid, \
  import  command_no_data_valid, \
  import  command_posted_ack, \
  import  command_non_posted_ack, \
  import  command_posted_valid, \
  import  command_non_posted_valid, \
  import  command_valid, \
  import  write_data_ack, \
  import  write_data_last_ack, \
  import  unpack_length, \
  import  get_length, \
  import  get_aligned_length, \
  import  get_burst_length, \
  import  get_response_length \
); \
\
modport command_master ( \
  input   scmd_accept, \
  output  mcmd_valid, \
  output  mcmd, \
  output  mid, \
  output  maddr, \
  output  mparam, \
  output  mlength, \
  output  minfo, \
  import  put_packed_command, \
  import  put_command, \
  import  is_non_posted_command, \
  import  is_posted_command, \
  import  is_command_with_data, \
  import  is_command_no_data, \
  import  is_command_with_response_data, \
  import  get_command_kind, \
  import  is_read_command, \
  import  is_write_command, \
  import  is_full_write_command, \
  import  is_broadcast_command, \
  import  is_write_access_command, \
  import  is_posted_write_acess_command, \
  import  is_non_posted_write_access_command, \
  import  is_atomic_command, \
  import  is_message_command, \
  import  command_ack, \
  import  command_with_data_ack, \
  import  command_no_data_ack, \
  import  command_with_data_valid, \
  import  command_no_data_valid, \
  import  command_posted_ack, \
  import  command_non_posted_ack, \
  import  command_posted_valid, \
  import  command_non_posted_valid, \
  import  command_valid, \
  import  unpack_length, \
  import  get_length, \
  import  get_aligned_length, \
  import  get_burst_length, \
  import  get_response_length \
); \
\
modport write_data_master ( \
  input   sdata_accept, \
  output  mdata_valid, \
  output  mdata, \
  output  mdata_byteen, \
  output  mdata_last, \
  import  put_packed_write_data, \
  import  put_write_data, \
  import  write_data_ack, \
  import  write_data_last_ack \
); \
\
modport request_slave ( \
  output  scmd_accept, \
  input   mcmd_valid, \
  input   mcmd, \
  input   mid, \
  input   maddr, \
  input   mlength, \
  input   mparam, \
  input   minfo, \
  output  sdata_accept, \
  input   mdata_valid, \
  input   mdata, \
  input   mdata_byteen, \
  input   mdata_last, \
  import  get_packed_command, \
  import  get_command, \
  import  get_packed_write_data, \
  import  get_write_data, \
  import  get_packed_request, \
  import  get_request, \
  import  is_non_posted_command, \
  import  is_posted_command, \
  import  is_command_with_data, \
  import  is_command_no_data, \
  import  is_command_with_response_data, \
  import  get_command_kind, \
  import  is_read_command, \
  import  is_write_command, \
  import  is_full_write_command, \
  import  is_broadcast_command, \
  import  is_write_access_command, \
  import  is_posted_write_acess_command, \
  import  is_non_posted_write_access_command, \
  import  is_atomic_command, \
  import  is_message_command, \
  import  command_ack, \
  import  command_with_data_ack, \
  import  command_no_data_ack, \
  import  command_with_data_valid, \
  import  command_no_data_valid, \
  import  command_posted_ack, \
  import  command_non_posted_ack, \
  import  command_posted_valid, \
  import  command_non_posted_valid, \
  import  command_valid, \
  import  write_data_ack, \
  import  write_data_last_ack, \
  import  unpack_length, \
  import  get_length, \
  import  get_aligned_length, \
  import  get_burst_length, \
  import  get_response_length \
); \
\
modport command_slave ( \
  output  scmd_accept, \
  input   mcmd_valid, \
  input   mcmd, \
  input   mid, \
  input   maddr, \
  input   mlength, \
  input   mparam, \
  input   minfo, \
  import  get_packed_command, \
  import  get_command, \
  import  is_non_posted_command, \
  import  is_posted_command, \
  import  is_command_with_data, \
  import  is_command_no_data, \
  import  is_command_with_response_data, \
  import  get_command_kind, \
  import  is_read_command, \
  import  is_write_command, \
  import  is_full_write_command, \
  import  is_broadcast_command, \
  import  is_write_access_command, \
  import  is_posted_write_acess_command, \
  import  is_non_posted_write_access_command, \
  import  is_atomic_command, \
  import  is_message_command, \
  import  command_ack, \
  import  command_with_data_ack, \
  import  command_no_data_ack, \
  import  command_with_data_valid, \
  import  command_no_data_valid, \
  import  command_posted_ack, \
  import  command_non_posted_ack, \
  import  command_posted_valid, \
  import  command_non_posted_valid, \
  import  command_valid, \
  import  unpack_length, \
  import  get_length, \
  import  get_aligned_length, \
  import  get_burst_length, \
  import  get_response_length \
); \
\
modport write_data_slave ( \
  output  sdata_accept, \
  input   mdata_valid, \
  input   mdata, \
  input   mdata_byteen, \
  input   mdata_last, \
  import  get_packed_write_data, \
  import  get_write_data, \
  import  write_data_ack, \
  import  write_data_last_ack \
); \
\
modport request_monitor ( \
  input   scmd_accept, \
  input   mcmd_valid, \
  input   mcmd, \
  input   mid, \
  input   maddr, \
  input   mlength, \
  input   mparam, \
  input   minfo, \
  input   sdata_accept, \
  input   mdata_valid, \
  input   mdata, \
  input   mdata_byteen, \
  input   mdata_last, \
  import  get_packed_command, \
  import  get_command, \
  import  get_packed_write_data, \
  import  get_write_data, \
  import  get_packed_request, \
  import  get_request, \
  import  is_non_posted_command, \
  import  is_posted_command, \
  import  is_command_with_data, \
  import  is_command_no_data, \
  import  is_command_with_response_data, \
  import  get_command_kind, \
  import  is_read_command, \
  import  is_write_command, \
  import  is_full_write_command, \
  import  is_broadcast_command, \
  import  is_write_access_command, \
  import  is_posted_write_acess_command, \
  import  is_non_posted_write_access_command, \
  import  is_atomic_command, \
  import  is_message_command, \
  import  command_ack, \
  import  command_with_data_ack, \
  import  command_no_data_ack, \
  import  command_with_data_valid, \
  import  command_no_data_valid, \
  import  command_posted_ack, \
  import  command_non_posted_ack, \
  import  command_posted_valid, \
  import  command_non_posted_valid, \
  import  command_valid, \
  import  write_data_ack, \
  import  write_data_last_ack, \
  import  unpack_length, \
  import  get_length, \
  import  get_aligned_length, \
  import  get_burst_length, \
  import  get_response_length \
);

`define pzcorebus_if_define_response_modports \
modport response_master ( \
  output  mresp_accept, \
  input   sresp_valid, \
  input   sresp, \
  input   sid, \
  input   serror, \
  input   sdata, \
  input   sinfo, \
  input   sresp_uniten, \
  input   sresp_last, \
  import  get_packed_response, \
  import  get_response, \
  import  response_ack, \
  import  response_last_ack, \
  import  response_last_burst_ack, \
  import  response_with_data_ack, \
  import  response_no_data_ack \
); \
\
modport response_slave ( \
  input   mresp_accept, \
  output  sresp_valid, \
  output  sresp, \
  output  sid, \
  output  serror, \
  output  sdata, \
  output  sinfo, \
  output  sresp_uniten, \
  output  sresp_last, \
  import  put_packed_response, \
  import  put_response, \
  import  response_ack, \
  import  response_last_ack, \
  import  response_last_burst_ack, \
  import  response_with_data_ack, \
  import  response_no_data_ack \
); \
\
modport response_monitor ( \
  input   mresp_accept, \
  input   sresp_valid, \
  input   sresp, \
  input   sid, \
  input   serror, \
  input   sdata, \
  input   sinfo, \
  input   sresp_uniten, \
  input   sresp_last, \
  import  get_packed_response, \
  import  get_response, \
  import  response_ack, \
  import  response_last_ack, \
  import  response_last_burst_ack, \
  import  response_with_data_ack, \
  import  response_no_data_ack \
);

`endif
