//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_if_packer
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG              = '0,
  localparam  int               PACKED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG),
  localparam  int               PACKED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1),
  localparam  int               PACKED_RESPONSE_WIDTH   = get_packed_response_width(BUS_CONFIG)
)(
  pzcorebus_if.slave                        corebus_if,
  output  var                               o_mcmd_valid,
  input   var                               i_scmd_accept,
  output  var [PACKED_COMMAND_WIDTH-1:0]    o_mcmd,
  output  var                               o_mdata_valid,
  input   var                               i_sdata_accept,
  output  var [PACKED_WRITE_DATA_WIDTH-1:0] o_mdata,
  input   var                               i_sresp_valid,
  output  var                               o_mresp_accept,
  input   var [PACKED_RESPONSE_WIDTH-1:0]   i_sresp
);
  always_comb begin
    corebus_if.scmd_accept  = i_scmd_accept;
    o_mcmd_valid            = corebus_if.mcmd_valid;
    o_mcmd                  = corebus_if.get_packed_command();

    corebus_if.sdata_accept = i_sdata_accept;
    o_mdata_valid           = corebus_if.mdata_valid;
    o_mdata                 = corebus_if.get_packed_write_data();
  end

  always_comb begin
    o_mresp_accept  = corebus_if.mresp_accept;
    corebus_if.sresp_valid  = i_sresp_valid;
    corebus_if.put_packed_response(i_sresp);
  end
endmodule

module pzcorebus_request_if_packer
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG              = '0,
  localparam  int               PACKED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG),
  localparam  int               PACKED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1)
)(
  interface.request_slave                   corebus_if,
  output  var                               o_mcmd_valid,
  input   var                               i_scmd_accept,
  output  var [PACKED_COMMAND_WIDTH-1:0]    o_mcmd,
  output  var                               o_mdata_valid,
  input   var                               i_sdata_accept,
  output  var [PACKED_WRITE_DATA_WIDTH-1:0] o_mdata
);
  always_comb begin
    corebus_if.scmd_accept  = i_scmd_accept;
    o_mcmd_valid            = corebus_if.mcmd_valid;
    o_mcmd                  = corebus_if.get_packed_command();

    corebus_if.sdata_accept = i_sdata_accept;
    o_mdata_valid           = corebus_if.mdata_valid;
    o_mdata                 = corebus_if.get_packed_write_data();
  end
endmodule

module pzcorebus_response_if_packer
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG            = '0,
  localparam  int               PACKED_RESPONSE_WIDTH = get_packed_response_width(BUS_CONFIG)
)(
  interface.response_slave                  corebus_if,
  input   var                               i_sresp_valid,
  output  var                               o_mresp_accept,
  input   var [PACKED_RESPONSE_WIDTH-1:0]   i_sresp
);
  always_comb begin
    o_mresp_accept  = corebus_if.mresp_accept;
    corebus_if.sresp_valid  = i_sresp_valid;
    corebus_if.put_packed_response(i_sresp);
  end
endmodule
