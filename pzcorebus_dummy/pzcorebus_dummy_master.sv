//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
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
    master_if.mparam        = '0;
    master_if.minfo         = '0;
    master_if.mdata_valid   = '0;
    master_if.mdata         = '0;
    master_if.mdata_byteen  = '0;
    master_if.mdata_last    = '0;
    master_if.mresp_accept  = '1;
  end
endmodule

module pzcorebus_array_dummy_master
  import  pzcorebus_pkg::*;
#(
  parameter int MASTERS = 2
)(
  pzcorebus_if.master master_if[MASTERS]
);
  for (genvar i = 0;i < MASTERS;++i) begin : g
    always_comb begin
      master_if[i].mcmd_valid   = '0;
      master_if[i].mcmd         = PZCOREBUS_NULL_COMMAND;
      master_if[i].mid          = '0;
      master_if[i].maddr        = '0;
      master_if[i].mlength      = '0;
      master_if[i].mparam       = '0;
      master_if[i].minfo        = '0;
      master_if[i].mdata_valid  = '0;
      master_if[i].mdata        = '0;
      master_if[i].mdata_byteen = '0;
      master_if[i].mdata_last   = '0;
      master_if[i].mresp_accept = '1;
    end
  end
endmodule
