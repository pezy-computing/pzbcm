//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_bundled_array_if_unpacker
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG        = '0,
  parameter   int               REQUEST_CHANNELS  = 1,
  parameter   int               RESPONSE_CHANNELS = 1,
  parameter   int               SIZE              = 1,
  localparam  int               COMMAND_WIDTH     = get_packed_command_width(BUS_CONFIG),
  localparam  int               WRITE_DATA_WIDTH  = get_packed_write_data_width(BUS_CONFIG, 1),
  localparam  int               RESPONSE_WIDTH    = get_packed_response_width(BUS_CONFIG)
)(
  pzcorebus_bundled_if.master                                         corebus_if[SIZE],
  output  var [SIZE-1:0][REQUEST_CHANNELS-1:0]                        o_scmd_accept,
  input   var [SIZE-1:0][REQUEST_CHANNELS-1:0]                        i_mcmd_valid,
  input   var [SIZE-1:0][REQUEST_CHANNELS-1:0][COMMAND_WIDTH-1:0]     i_mcmd,
  output  var [SIZE-1:0][REQUEST_CHANNELS-1:0]                        o_sdata_accept,
  input   var [SIZE-1:0][REQUEST_CHANNELS-1:0]                        i_mdata_valid,
  input   var [SIZE-1:0][REQUEST_CHANNELS-1:0][WRITE_DATA_WIDTH-1:0]  i_mdata,
  input   var [SIZE-1:0][RESPONSE_CHANNELS-1:0]                       i_mresp_accept,
  output  var [SIZE-1:0][RESPONSE_CHANNELS-1:0]                       o_sresp_valid,
  output  var [SIZE-1:0][RESPONSE_CHANNELS-1:0][RESPONSE_WIDTH-1:0]   o_sresp
);
  initial begin
    assume (corebus_if[0].REQUEST_CHANNELS  == REQUEST_CHANNELS);
    assume (corebus_if[0].RESPONSE_CHANNELS == RESPONSE_CHANNELS);
  end

  for (genvar i = 0;i < SIZE;++i) begin : g
    always_comb begin
      o_scmd_accept[i]          = corebus_if[i].scmd_accept;
      corebus_if[i].mcmd_valid  = i_mcmd_valid[i];
      corebus_if[i].mcmd        = i_mcmd[i];
      o_sdata_accept[i]         = corebus_if[i].sdata_accept;
      corebus_if[i].mdata_valid = i_mdata_valid[i];
      corebus_if[i].mdata       = i_mdata[i];
    end

    always_comb begin
      corebus_if[i].mresp_accept  = i_mresp_accept[i];
      o_sresp_valid[i]            = corebus_if[i].sresp_valid;
      o_sresp[i]                  = corebus_if[i].sresp;
    end
  end
endmodule
