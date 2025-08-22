//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
interface pzcorebus_bundled_if
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               REQUEST_CHANNELS  = 1,
  parameter int               RESPONSE_CHANNELS = 1
);
  localparam  int PAKCED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG);
  localparam  int PACKED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1);
  localparam  int PACKED_RESPONSE_WIDTH   = get_packed_response_width(BUS_CONFIG);

  logic [REQUEST_CHANNELS-1:0]                              scmd_accept;
  logic [REQUEST_CHANNELS-1:0]                              mcmd_valid;
  logic [REQUEST_CHANNELS-1:0][PAKCED_COMMAND_WIDTH-1:0]    mcmd;
  logic [REQUEST_CHANNELS-1:0]                              sdata_accept;
  logic [REQUEST_CHANNELS-1:0]                              mdata_valid;
  logic [REQUEST_CHANNELS-1:0][PACKED_WRITE_DATA_WIDTH-1:0] mdata;
  logic [RESPONSE_CHANNELS-1:0]                             mresp_accept;
  logic [RESPONSE_CHANNELS-1:0]                             sresp_valid;
  logic [RESPONSE_CHANNELS-1:0][PACKED_RESPONSE_WIDTH-1:0]  sresp;

  modport master (
    input   scmd_accept,
    output  mcmd_valid,
    output  mcmd,
    input   sdata_accept,
    output  mdata_valid,
    output  mdata,
    output  mresp_accept,
    input   sresp_valid,
    input   sresp
  );

  modport slave (
    output  scmd_accept,
    input   mcmd_valid,
    input   mcmd,
    output  sdata_accept,
    input   mdata_valid,
    input   mdata,
    input   mresp_accept,
    output  sresp_valid,
    output  sresp
  );

  modport monitor (
    input scmd_accept,
    input mcmd_valid,
    input mcmd,
    input sdata_accept,
    input mdata_valid,
    input mdata,
    input mresp_accept,
    input sresp_valid,
    input sresp
  );
endinterface
