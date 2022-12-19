//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_if_bundler
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               REQUEST_CHANNELS  = 1,
  parameter int               RESPONSE_CHANNELS = 1
)(
  interface.request_slave     request_if[REQUEST_CHANNELS],
  interface.response_slave    response_if[RESPONSE_CHANNELS],
  pzcorebus_bundled_if.master bundled_if
);
  initial begin
    assume (bundled_if.REQUEST_CHANNELS  == REQUEST_CHANNELS);
    assume (bundled_if.RESPONSE_CHANNELS == RESPONSE_CHANNELS);
  end

  for (genvar i = 0;i < REQUEST_CHANNELS;++i) begin : g_request
    always_comb begin
      request_if[i].scmd_accept = bundled_if.scmd_accept[i];
      bundled_if.mcmd_valid[i]  = request_if[i].mcmd_valid;
      bundled_if.mcmd[i]        = request_if[i].get_packed_command();

      request_if[i].sdata_accept  = bundled_if.sdata_accept[i];
      bundled_if.mdata_valid[i]   = request_if[i].mdata_valid;
      bundled_if.mdata[i]         = request_if[i].get_packed_write_data();
    end
  end

  for (genvar i = 0;i < RESPONSE_CHANNELS;++i) begin : g_response
    always_comb begin
      bundled_if.mresp_accept[i]  = response_if[i].mresp_accept;
      response_if[i].sresp_valid  = bundled_if.sresp_valid[i];
      response_if[i].put_packed_response(bundled_if.sresp[i]);
    end
  end
endmodule
