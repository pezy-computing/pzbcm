//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_request_dummy_slave
  import  pzcorebus_pkg::*;
(
  interface.request_slave slave_if
);
  always_comb begin
    slave_if.scmd_accept  = '0;
    slave_if.sdata_accept = '0;
  end
endmodule
