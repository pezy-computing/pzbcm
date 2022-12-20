//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_base_address_remover
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG    = '0,
  parameter int               ADDRESS_WIDTH = BUS_CONFIG.address_width
)(
  input var [ADDRESS_WIDTH-1:0] i_base_mask,
  pzcorebus_if.slave            slave_if,
  pzcorebus_if.master           master_if
);
  always_comb begin
    slave_if.scmd_accept  = master_if.scmd_accept;
    master_if.mcmd_valid  = slave_if.mcmd_valid;
    master_if.mcmd        = slave_if.mcmd;
    master_if.mid         = slave_if.mid;
    master_if.maddr       = slave_if.maddr & (~i_base_mask);
    master_if.mlength     = slave_if.mlength;
    master_if.minfo       = slave_if.minfo;
  end

  always_comb begin
    slave_if.sdata_accept   = master_if.sdata_accept;
    master_if.mdata_valid   = slave_if.mdata_valid;
    master_if.mdata         = slave_if.mdata;
    master_if.mdata_byteen  = slave_if.mdata_byteen;
    master_if.mdata_last    = slave_if.mdata_last;
  end

  always_comb begin
    master_if.mresp_accept  = slave_if.mresp_accept;
    slave_if.sresp_valid    = master_if.sresp_valid;
    slave_if.sresp          = master_if.sresp;
    slave_if.sid            = master_if.sid;
    slave_if.serror         = master_if.serror;
    slave_if.sdata          = master_if.sdata;
    slave_if.sinfo          = master_if.sinfo;
    slave_if.sresp_uniten   = master_if.sresp_uniten;
    slave_if.sresp_last     = master_if.sresp_last;
  end
endmodule
