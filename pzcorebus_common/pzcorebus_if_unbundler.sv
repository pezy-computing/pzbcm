//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_if_unbundler
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               REQUEST_CHANNELS  = 1,
  parameter int               RESPONSE_CHANNELS = 1
)(
  pzcorebus_bundled_if.slave  bundled_if,
  interface.request_master    request_if[REQUEST_CHANNELS],
  interface.response_master   response_if[RESPONSE_CHANNELS]
);
  initial begin
    assume (bundled_if.REQUEST_CHANNELS  == REQUEST_CHANNELS);
    assume (bundled_if.RESPONSE_CHANNELS == RESPONSE_CHANNELS);
  end

  for (genvar i = 0;i < REQUEST_CHANNELS;++i) begin : g_request
    always_comb begin
      bundled_if.scmd_accept[i] = request_if[i].scmd_accept;
      request_if[i].mcmd_valid  = bundled_if.mcmd_valid[i];
      request_if[i].put_packed_command(bundled_if.mcmd[i]);

      bundled_if.sdata_accept[i]  = request_if[i].sdata_accept;
      request_if[i].mdata_valid   = bundled_if.mdata_valid[i];
      request_if[i].put_packed_write_data(bundled_if.mdata[i]);
    end
  end

  for (genvar i = 0;i < RESPONSE_CHANNELS;++i) begin : g_response
    always_comb begin
      response_if[i].mresp_accept = bundled_if.mresp_accept[i];
      bundled_if.sresp_valid[i]   = response_if[i].sresp_valid;
      bundled_if.sresp[i]         = response_if[i].get_packed_response();
    end
  end
endmodule
