//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_dummy_master
  import  pzcorebus_pkg::*;
(
  pzcorebus_if.master master_if
);
  always_comb begin
    master_if.mcmd_valid    = '0;
    master_if.mcmd          = PZCOREBUS_NULL_COMMAND;
    master_if.mid           = '0;
    master_if.maddr         = '0;
    master_if.mlength       = '0;
    master_if.minfo         = '0;
    master_if.mdata_valid   = '0;
    master_if.mdata         = '0;
    master_if.mdata_byteen  = '0;
    master_if.mdata_last    = '0;
    master_if.mresp_accept  = '1;
  end
endmodule
