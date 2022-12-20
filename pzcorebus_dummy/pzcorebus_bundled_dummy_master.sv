//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_bundled_dummy_master (
  pzcorebus_bundled_if.master master_if
);
  always_comb begin
    master_if.mcmd_valid    = '0;
    master_if.mcmd          = '0;
    master_if.mdata_valid   = '0;
    master_if.mdata         = '0;
    master_if.mresp_accept  = '0;
  end
endmodule
