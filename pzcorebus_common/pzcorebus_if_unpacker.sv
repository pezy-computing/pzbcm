//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_if_unpacker
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG              = '0,
  localparam  int               PACKED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG),
  localparam  int               PACKED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1),
  localparam  int               PACKED_RESPONSE_WIDTH   = get_packed_response_width(BUS_CONFIG)
)(
  pzcorebus_if.master                       corebus_if,
  input   var                               i_mcmd_valid,
  output  var                               o_scmd_accept,
  input   var [PACKED_COMMAND_WIDTH-1:0]    i_mcmd,
  input   var                               i_mdata_valid,
  output  var                               o_sdata_accept,
  input   var [PACKED_WRITE_DATA_WIDTH-1:0] i_mdata,
  output  var                               o_sresp_valid,
  input   var                               i_mresp_accept,
  output  var [PACKED_RESPONSE_WIDTH-1:0]   o_sresp
);
  always_comb begin
    o_scmd_accept         = corebus_if.scmd_accept;
    corebus_if.mcmd_valid = i_mcmd_valid;
    corebus_if.put_packed_command(i_mcmd);

    o_sdata_accept          = corebus_if.sdata_accept;
    corebus_if.mdata_valid  = i_mdata_valid;
    corebus_if.put_packed_write_data(i_mdata);
  end

  always_comb begin
    corebus_if.mresp_accept = i_mresp_accept;
    o_sresp_valid           = corebus_if.sresp_valid;
    o_sresp                 = corebus_if.get_packed_response();
  end
endmodule

module pzcorebus_request_if_unpacker
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG              = '0,
  localparam  int               PACKED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG),
  localparam  int               PACKED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1)
)(
  interface.request_master                  corebus_if,
  input   var                               i_mcmd_valid,
  output  var                               o_scmd_accept,
  input   var [PACKED_COMMAND_WIDTH-1:0]    i_mcmd,
  input   var                               i_mdata_valid,
  output  var                               o_sdata_accept,
  input   var [PACKED_WRITE_DATA_WIDTH-1:0] i_mdata
);
  always_comb begin
    o_scmd_accept         = corebus_if.scmd_accept;
    corebus_if.mcmd_valid = i_mcmd_valid;
    corebus_if.put_packed_command(i_mcmd);

    o_sdata_accept          = corebus_if.sdata_accept;
    corebus_if.mdata_valid  = i_mdata_valid;
    corebus_if.put_packed_write_data(i_mdata);
  end
endmodule

module pzcorebus_response_if_unpacker
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG            = '0,
  localparam  int               PACKED_RESPONSE_WIDTH = get_packed_response_width(BUS_CONFIG)
)(
  interface.response_master               corebus_if,
  output  var                             o_sresp_valid,
  input   var                             i_mresp_accept,
  output  var [PACKED_RESPONSE_WIDTH-1:0] o_sresp
);
  always_comb begin
    corebus_if.mresp_accept = i_mresp_accept;
    o_sresp_valid           = corebus_if.sresp_valid;
    o_sresp                 = corebus_if.get_packed_response();
  end
endmodule
