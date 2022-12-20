//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_array_if_packer
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG        = '0,
  parameter   int               SIZE              = 1,
  localparam  int               COMMAND_WIDTH     = get_packed_command_width(BUS_CONFIG),
  localparam  int               WRITE_DATA_WIDTH  = get_packed_write_data_width(BUS_CONFIG, 1),
  localparam  int               RESPONSE_WIDTH    = get_packed_response_width(BUS_CONFIG)
)(
  pzcorebus_if.slave                            corebus_if[SIZE],
  output  var [SIZE-1:0]                        o_mcmd_valid,
  input   var [SIZE-1:0]                        i_scmd_accept,
  output  var [SIZE-1:0][COMMAND_WIDTH-1:0]     o_mcmd,
  output  var [SIZE-1:0]                        o_mdata_valid,
  input   var [SIZE-1:0]                        i_sdata_accept,
  output  var [SIZE-1:0][WRITE_DATA_WIDTH-1:0]  o_mdata,
  input   var [SIZE-1:0]                        i_sresp_valid,
  output  var [SIZE-1:0]                        o_mresp_accept,
  input   var [SIZE-1:0][RESPONSE_WIDTH-1:0]    i_sresp
);
  for (genvar i = 0;i < SIZE;++i) begin : g
    always_comb begin
      corebus_if[i].scmd_accept = i_scmd_accept[i];
      o_mcmd_valid[i]           = corebus_if[i].mcmd_valid;
      o_mcmd[i]                 = corebus_if[i].get_packed_command();

      corebus_if[i].sdata_accept  = i_sdata_accept[i];
      o_mdata_valid[i]            = corebus_if[i].mdata_valid;
      o_mdata[i]                  = corebus_if[i].get_packed_write_data();
    end

    always_comb begin
      o_mresp_accept[i]         = corebus_if[i].mresp_accept;
      corebus_if[i].sresp_valid = i_sresp_valid[i];
      corebus_if[i].put_packed_response(i_sresp[i]);
    end
  end
endmodule

module pzcorebus_request_array_if_packer
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG        = '0,
  parameter   int               SIZE              = 1,
  localparam  int               COMMAND_WIDTH     = get_packed_command_width(BUS_CONFIG),
  localparam  int               WRITE_DATA_WIDTH  = get_packed_write_data_width(BUS_CONFIG, 1)
)(
  interface.request_slave                       corebus_if[SIZE],
  output  var [SIZE-1:0]                        o_mcmd_valid,
  input   var [SIZE-1:0]                        i_scmd_accept,
  output  var [SIZE-1:0][COMMAND_WIDTH-1:0]     o_mcmd,
  output  var [SIZE-1:0]                        o_mdata_valid,
  input   var [SIZE-1:0]                        i_sdata_accept,
  output  var [SIZE-1:0][WRITE_DATA_WIDTH-1:0]  o_mdata
);
  for (genvar i = 0;i < SIZE;++i) begin : g
    always_comb begin
      corebus_if[i].scmd_accept = i_scmd_accept[i];
      o_mcmd_valid[i]           = corebus_if[i].mcmd_valid;
      o_mcmd[i]                 = corebus_if[i].get_packed_command();

      corebus_if[i].sdata_accept  = i_sdata_accept[i];
      o_mdata_valid[i]            = corebus_if[i].mdata_valid;
      o_mdata[i]                  = corebus_if[i].get_packed_write_data();
    end
  end
endmodule

module pzcorebus_response_array_if_packer
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG      = '0,
  parameter   int               SIZE            = 1,
  localparam  int               RESPONSE_WIDTH  = get_packed_response_width(BUS_CONFIG)
)(
  interface.response_slave                    corebus_if[SIZE],
  input   var [SIZE-1:0]                      i_sresp_valid,
  output  var [SIZE-1:0]                      o_mresp_accept,
  input   var [SIZE-1:0][RESPONSE_WIDTH-1:0]  i_sresp
);
  for (genvar i = 0;i < SIZE;++i) begin : g
    always_comb begin
      o_mresp_accept[i]         = corebus_if[i].mresp_accept;
      corebus_if[i].sresp_valid = i_sresp_valid[i];
      corebus_if[i].put_packed_response(i_sresp[i]);
    end
  end
endmodule
