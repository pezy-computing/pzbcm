//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_id_assigner
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG            = '0,
  parameter   int               ID_WIDTH              = BUS_CONFIG.id_width,
  parameter   int               LOCAL_ID_WIDTH        = ID_WIDTH - 1,
  parameter   int               LOCAL_ID_LSB          = 0,
  parameter   int               BASE_ID_WIDTH         = ID_WIDTH - LOCAL_ID_WIDTH,
  parameter   int               BASE_ID_LSB           = LOCAL_ID_WIDTH,
  localparam  int               BASE_ID_ACTUAL_WIDTH  = (BASE_ID_WIDTH > 0) ? BASE_ID_WIDTH : 1
)(
  input var [BASE_ID_ACTUAL_WIDTH-1:0]  i_base_id,
  pzcorebus_if.slave                    slave_if,
  pzcorebus_if.master                   master_if
);
  localparam  bit [ID_WIDTH-1:0]  LOCAL_ID_MASK = (1 << LOCAL_ID_WIDTH) - 1;

  function automatic logic [ID_WIDTH-1:0] get_mid(
    logic [BASE_ID_ACTUAL_WIDTH-1:0]  base_id,
    logic [ID_WIDTH-1:0]              local_id
  );
    return
      ID_WIDTH'(base_id << BASE_ID_LSB) |
      ID_WIDTH'((local_id & LOCAL_ID_MASK) << LOCAL_ID_LSB);
  endfunction

  always_comb begin
    slave_if.scmd_accept  = master_if.scmd_accept;
    master_if.mcmd_valid  = slave_if.mcmd_valid;
    master_if.mcmd        = slave_if.mcmd;
    master_if.mid         = get_mid(i_base_id, slave_if.mid);
    master_if.maddr       = slave_if.maddr;
    master_if.mlength     = slave_if.mlength;
    master_if.mparam      = slave_if.mparam;
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
    slave_if.sid            = get_sid(master_if.sid);
    slave_if.serror         = master_if.serror;
    slave_if.sdata          = master_if.sdata;
    slave_if.sinfo          = master_if.sinfo;
    slave_if.sresp_uniten   = master_if.sresp_uniten;
    slave_if.sresp_last     = master_if.sresp_last;
  end

  function automatic logic [ID_WIDTH-1:0] get_sid(
    logic [ID_WIDTH-1:0]  id
  );
    return ID_WIDTH'((id >> LOCAL_ID_LSB) & LOCAL_ID_MASK);
  endfunction
endmodule

module pzcorebus_request_id_assigner
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG            = '0,
  parameter   int               ID_WIDTH              = BUS_CONFIG.id_width,
  parameter   int               LOCAL_ID_WIDTH        = ID_WIDTH - 1,
  parameter   int               LOCAL_ID_LSB          = 0,
  parameter   int               BASE_ID_WIDTH         = ID_WIDTH - LOCAL_ID_WIDTH,
  parameter   int               BASE_ID_LSB           = LOCAL_ID_WIDTH,
  localparam  int               BASE_ID_ACTUAL_WIDTH  = (BASE_ID_WIDTH > 0) ? BASE_ID_WIDTH : 1
)(
  input var [BASE_ID_ACTUAL_WIDTH-1:0]  i_base_id,
  interface.request_slave               slave_if,
  interface.request_master              master_if
);
  localparam  bit [ID_WIDTH-1:0]  LOCAL_ID_MASK = (1 << LOCAL_ID_WIDTH) - 1;

  function automatic logic [ID_WIDTH-1:0] get_mid(
    logic [BASE_ID_ACTUAL_WIDTH-1:0]  base_id,
    logic [ID_WIDTH-1:0]              local_id
  );
    return
      ID_WIDTH'(base_id << BASE_ID_LSB) |
      ID_WIDTH'((local_id & LOCAL_ID_MASK) << LOCAL_ID_LSB);
  endfunction

  always_comb begin
    slave_if.scmd_accept  = master_if.scmd_accept;
    master_if.mcmd_valid  = slave_if.mcmd_valid;
    master_if.mcmd        = slave_if.mcmd;
    master_if.mid         = get_mid(i_base_id, slave_if.mid);
    master_if.maddr       = slave_if.maddr;
    master_if.mlength     = slave_if.mlength;
    master_if.mparam      = slave_if.mparam;
    master_if.minfo       = slave_if.minfo;
  end

  always_comb begin
    slave_if.sdata_accept   = master_if.sdata_accept;
    master_if.mdata_valid   = slave_if.mdata_valid;
    master_if.mdata         = slave_if.mdata;
    master_if.mdata_byteen  = slave_if.mdata_byteen;
    master_if.mdata_last    = slave_if.mdata_last;
  end
endmodule

module pzcorebus_response_id_remover
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG      = '0,
  parameter int               ID_WIDTH        = BUS_CONFIG.id_width,
  parameter int               LOCAL_ID_WIDTH  = ID_WIDTH - 1,
  parameter int               LOCAL_ID_LSB    = 0
)(
  interface.response_slave  slave_if,
  interface.response_master master_if
);
  localparam  bit [ID_WIDTH-1:0]  LOCAL_ID_MASK = (1 << LOCAL_ID_WIDTH) - 1;

  always_comb begin
    master_if.mresp_accept  = slave_if.mresp_accept;
    slave_if.sresp_valid    = master_if.sresp_valid;
    slave_if.sresp          = master_if.sresp;
    slave_if.sid            = get_sid(master_if.sid);
    slave_if.serror         = master_if.serror;
    slave_if.sdata          = master_if.sdata;
    slave_if.sinfo          = master_if.sinfo;
    slave_if.sresp_uniten   = master_if.sresp_uniten;
    slave_if.sresp_last     = master_if.sresp_last;
  end
  function automatic logic [ID_WIDTH-1:0] get_sid(
    logic [ID_WIDTH-1:0]  id
  );
    return ID_WIDTH'((id >> LOCAL_ID_LSB) & LOCAL_ID_MASK);
  endfunction
endmodule
