//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzcorebus_if
  import  pzcorebus_pkg::*,
          pzcorebus_if_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG  = '0
);
  `include  "pzcorebus_if_internal_macros.svh"
  `include  "pzcorebus_macros.svh"

//--------------------------------------------------------------
//  Type Definitions
//--------------------------------------------------------------
  `pzcorebus_if_define_types(BUS_CONFIG)

//--------------------------------------------------------------
//  Signal Declarations
//--------------------------------------------------------------
  `pzcorebus_if_declare_request_signals
  `pzcorebus_if_declare_response_signals

//--------------------------------------------------------------
//  Debug
//--------------------------------------------------------------
  if (PZCOREBUS_ENABLE_DEBUG) begin : g_debug
    logic [BUS_CONFIG.data_width/32-1:0][31:0]  debug_mdata;
    logic [BUS_CONFIG.data_width/32-1:0][3:0]   debug_mdata_byteen;
    logic [BUS_CONFIG.data_width/32-1:0][31:0]  debug_sdata;

    always_comb begin
      debug_mdata         = mdata;
      debug_mdata_byteen  = mdata_byteen;
      debug_sdata         = sdata;
    end
  end

//--------------------------------------------------------------
//  API
//--------------------------------------------------------------
  `pzcorebus_if_define_request_api(BUS_CONFIG)
  `pzcorebus_if_define_response_api(BUS_CONFIG)

//--------------------------------------------------------------
//  Modport
//--------------------------------------------------------------
  modport master (
    input   scmd_accept,
    output  mcmd_valid,
    output  mcmd,
    output  mid,
    output  maddr,
    output  mlength,
    output  mparam,
    output  minfo,
    input   sdata_accept,
    output  mdata_valid,
    output  mdata,
    output  mdata_byteen,
    output  mdata_last,
    output  mresp_accept,
    input   sresp_valid,
    input   sresp,
    input   sid,
    input   serror,
    input   sdata,
    input   sinfo,
    input   sresp_uniten,
    input   sresp_last,
    import  put_packed_command,
    import  put_command,
    import  put_packed_write_data,
    import  put_write_data,
    import  put_packed_request,
    import  put_request,
    import  get_packed_response,
    import  get_response,
    import  is_non_posted_command,
    import  is_posted_command,
    import  is_command_with_data,
    import  is_command_no_data,
    import  is_command_with_response_data,
    import  get_command_kind,
    import  is_read_command,
    import  is_write_command,
    import  is_full_write_command,
    import  is_broadcast_command,
    import  is_write_access_command,
    import  is_posted_write_acess_command,
    import  is_non_posted_write_access_command,
    import  is_atomic_command,
    import  is_message_command,
    import  command_ack,
    import  command_with_data_ack,
    import  command_no_data_ack,
    import  command_with_data_valid,
    import  command_no_data_valid,
    import  command_posted_ack,
    import  command_non_posted_ack,
    import  command_posted_valid,
    import  command_non_posted_valid,
    import  command_valid,
    import  write_data_ack,
    import  write_data_last_ack,
    import  response_ack,
    import  response_last_ack,
    import  response_last_burst_ack,
    import  response_with_data_ack,
    import  response_no_data_ack,
    import  unpack_length,
    import  get_length,
    import  get_aligned_length,
    import  get_burst_length,
    import  get_response_length
  );

  modport slave (
    output  scmd_accept,
    input   mcmd_valid,
    input   mcmd,
    input   mid,
    input   maddr,
    input   mparam,
    input   mlength,
    input   minfo,
    output  sdata_accept,
    input   mdata_valid,
    input   mdata,
    input   mdata_byteen,
    input   mdata_last,
    input   mresp_accept,
    output  sresp_valid,
    output  sresp,
    output  sid,
    output  serror,
    output  sdata,
    output  sinfo,
    output  sresp_uniten,
    output  sresp_last,
    import  get_packed_command,
    import  get_command,
    import  get_packed_write_data,
    import  get_write_data,
    import  get_packed_request,
    import  get_request,
    import  put_packed_response,
    import  put_response,
    import  is_non_posted_command,
    import  is_posted_command,
    import  is_command_with_data,
    import  is_command_no_data,
    import  is_command_with_response_data,
    import  get_command_kind,
    import  is_read_command,
    import  is_write_command,
    import  is_full_write_command,
    import  is_broadcast_command,
    import  is_write_access_command,
    import  is_posted_write_acess_command,
    import  is_non_posted_write_access_command,
    import  is_atomic_command,
    import  is_message_command,
    import  command_ack,
    import  command_with_data_ack,
    import  command_no_data_ack,
    import  command_with_data_valid,
    import  command_no_data_valid,
    import  command_posted_ack,
    import  command_non_posted_ack,
    import  command_posted_valid,
    import  command_non_posted_valid,
    import  command_valid,
    import  write_data_ack,
    import  write_data_last_ack,
    import  response_ack,
    import  response_last_ack,
    import  response_last_burst_ack,
    import  response_with_data_ack,
    import  response_no_data_ack,
    import  unpack_length,
    import  get_length,
    import  get_aligned_length,
    import  get_burst_length,
    import  get_response_length
  );

  modport monitor (
    input   scmd_accept,
    input   mcmd_valid,
    input   mcmd,
    input   mid,
    input   maddr,
    input   mlength,
    input   mparam,
    input   minfo,
    input   sdata_accept,
    input   mdata_valid,
    input   mdata,
    input   mdata_byteen,
    input   mdata_last,
    input   mresp_accept,
    input   sresp_valid,
    input   sresp,
    input   sid,
    input   serror,
    input   sdata,
    input   sinfo,
    input   sresp_uniten,
    input   sresp_last,
    import  get_packed_command,
    import  get_command,
    import  get_packed_write_data,
    import  get_write_data,
    import  get_packed_request,
    import  get_request,
    import  get_packed_response,
    import  get_response,
    import  is_non_posted_command,
    import  is_posted_command,
    import  is_command_with_data,
    import  is_command_no_data,
    import  is_command_with_response_data,
    import  get_command_kind,
    import  is_read_command,
    import  is_write_command,
    import  is_full_write_command,
    import  is_broadcast_command,
    import  is_write_access_command,
    import  is_posted_write_acess_command,
    import  is_non_posted_write_access_command,
    import  is_atomic_command,
    import  is_message_command,
    import  command_ack,
    import  command_with_data_ack,
    import  command_no_data_ack,
    import  command_with_data_valid,
    import  command_no_data_valid,
    import  command_posted_ack,
    import  command_non_posted_ack,
    import  command_posted_valid,
    import  command_non_posted_valid,
    import  command_valid,
    import  write_data_ack,
    import  write_data_last_ack,
    import  response_ack,
    import  response_last_ack,
    import  response_last_burst_ack,
    import  response_with_data_ack,
    import  response_no_data_ack,
    import  unpack_length,
    import  get_length,
    import  get_aligned_length,
    import  get_burst_length,
    import  get_response_length
  );

  modport monitor_out (
    output  mcmd_valid,
    output  scmd_accept,
    output  mcmd,
    output  mid,
    output  maddr,
    output  mlength,
    output  mparam,
    output  minfo,
    output  mdata_valid,
    output  sdata_accept,
    output  mdata,
    output  mdata_byteen,
    output  mdata_last,
    output  sresp_valid,
    output  mresp_accept,
    output  sresp,
    output  sid,
    output  serror,
    output  sdata,
    output  sinfo,
    output  sresp_uniten,
    output  sresp_last,
    import  put_packed_command,
    import  put_command,
    import  put_packed_write_data,
    import  put_write_data,
    import  put_packed_request,
    import  put_request,
    import  put_packed_response,
    import  put_response,
    import  is_non_posted_command,
    import  is_posted_command,
    import  is_command_with_data,
    import  is_command_no_data,
    import  is_command_with_response_data,
    import  get_command_kind,
    import  is_read_command,
    import  is_write_command,
    import  is_full_write_command,
    import  is_broadcast_command,
    import  is_write_access_command,
    import  is_posted_write_acess_command,
    import  is_non_posted_write_access_command,
    import  is_atomic_command,
    import  is_message_command,
    import  command_ack,
    import  command_with_data_ack,
    import  command_no_data_ack,
    import  command_with_data_valid,
    import  command_no_data_valid,
    import  command_posted_ack,
    import  command_non_posted_ack,
    import  command_posted_valid,
    import  command_non_posted_valid,
    import  write_data_ack,
    import  write_data_last_ack,
    import  response_ack,
    import  response_last_ack,
    import  response_last_burst_ack,
    import  response_with_data_ack,
    import  response_no_data_ack,
    import  unpack_length,
    import  get_length,
    import  get_aligned_length,
    import  get_burst_length,
    import  get_response_length
  );

  `pzcorebus_if_define_request_modports
  `pzcorebus_if_define_response_modports
endinterface
