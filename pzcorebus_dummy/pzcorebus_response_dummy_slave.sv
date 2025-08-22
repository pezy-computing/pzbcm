//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_response_dummy_slave
  import  pzcorebus_pkg::*;
(
  interface.response_slave  slave_if
);
  always_comb begin
    slave_if.sresp_valid  = '0;
    slave_if.sresp        = pzcorebus_response_type'(0);
    slave_if.sid          = '0;
    slave_if.serror       = '0;
    slave_if.sdata        = '0;
    slave_if.sinfo        = '0;
    slave_if.sresp_uniten = '0;
    slave_if.sresp_last   = '0;
  end
endmodule
