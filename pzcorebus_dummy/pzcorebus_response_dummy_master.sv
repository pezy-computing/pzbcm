//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_response_dummy_master
  import  pzcorebus_pkg::*;
(
  interface.response_master master_if
);
  always_comb begin
    master_if.mresp_accept  = '0;
  end
endmodule
