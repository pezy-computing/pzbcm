//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_bundled_dummy_slave (
  pzcorebus_bundled_if.slave  slave_if
);
  always_comb begin
    slave_if.scmd_accept  = '0;
    slave_if.sdata_accept = '0;
    slave_if.sresp_valid  = '0;
    slave_if.sresp        = '0;
  end
endmodule
