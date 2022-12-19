//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_demux
  import  pzcorebus_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config    BUS_CONFIG              = '0,
  parameter int                 MASTERS                 = 2,
  parameter pzbcm_selector_type SELECTOR_TYPE           = PZBCM_SELECTOR_ONEHOT,
  parameter pzbcm_selector_type REQUEST_SELECTOR_TYPE   = SELECTOR_TYPE,
  parameter pzbcm_selector_type RESPONSE_SELECTOR_TYPE  = SELECTOR_TYPE,
  parameter int                 REQUEST_SELECT_WIDTH    = calc_select_width(REQUEST_SELECTOR_TYPE, MASTERS),
  parameter int                 RESPONSE_SELECT_WIDTH   = calc_select_width(RESPONSE_SELECTOR_TYPE, MASTERS)
)(
  input var [REQUEST_SELECT_WIDTH-1:0]  i_command_select,
  input var [REQUEST_SELECT_WIDTH-1:0]  i_write_data_select,
  input var [RESPONSE_SELECT_WIDTH-1:0] i_response_select,
  pzcorebus_if.slave                    slave_if,
  pzcorebus_if.master                   master_if[MASTERS]
);
  typedef logic [get_packed_command_width(BUS_CONFIG)-1:0]        pzcorebus_packed_command;
  typedef logic [get_packed_write_data_width(BUS_CONFIG, 1)-1:0]  pzcorebus_packed_write_data;
  typedef logic [get_packed_response_width(BUS_CONFIG)-1:0]       pzcorebus_packed_response;

  logic                                   slave_mcmd_valid;
  logic                                   slave_scmd_accept;
  pzcorebus_packed_command                slave_mcmd;
  logic                                   slave_mdata_valid;
  logic                                   slave_sdata_accept;
  pzcorebus_packed_write_data             slave_mdata;
  logic                                   slave_sresp_valid;
  logic                                   slave_mresp_accept;
  pzcorebus_packed_response               slave_sresp;
  logic [MASTERS-1:0]                     master_mcmd_valid;
  logic [MASTERS-1:0]                     master_scmd_accept;
  pzcorebus_packed_command                master_mcmd;
  logic [MASTERS-1:0]                     master_mdata_valid;
  logic [MASTERS-1:0]                     master_sdata_accept;
  pzcorebus_packed_write_data             master_mdata;
  logic [MASTERS-1:0]                     master_sresp_valid;
  logic [MASTERS-1:0]                     master_mresp_accept;
  pzcorebus_packed_response [MASTERS-1:0] master_sresp;

  pzbcm_selector #(
    .WIDTH          (1                      ),
    .ENTRIES        (MASTERS                ),
    .SELECTOR_TYPE  (REQUEST_SELECTOR_TYPE  )
  ) u_request_vaid_accept_selector();

  pzbcm_selector #(
    .WIDTH          (1                      ),
    .ENTRIES        (MASTERS                ),
    .SELECTOR_TYPE  (RESPONSE_SELECTOR_TYPE )
  ) u_response_vaid_accept_selector();

  pzbcm_selector #(
    .TYPE           (pzcorebus_packed_response  ),
    .ENTRIES        (MASTERS                    ),
    .SELECTOR_TYPE  (RESPONSE_SELECTOR_TYPE     )
  ) u_response_selector();

  pzcorebus_if_packer #(BUS_CONFIG) u_packer (
    .corebus_if     (slave_if           ),
    .o_mcmd_valid   (slave_mcmd_valid   ),
    .i_scmd_accept  (slave_scmd_accept  ),
    .o_mcmd         (slave_mcmd         ),
    .o_mdata_valid  (slave_mdata_valid  ),
    .i_sdata_accept (slave_sdata_accept ),
    .o_mdata        (slave_mdata        ),
    .i_sresp_valid  (slave_sresp_valid  ),
    .o_mresp_accept (slave_mresp_accept ),
    .i_sresp        (slave_sresp        )
  );

  always_comb begin
    slave_scmd_accept = u_request_vaid_accept_selector.mux(i_command_select, master_scmd_accept);
    master_mcmd_valid = u_request_vaid_accept_selector.demux(i_command_select, slave_mcmd_valid);
    master_mcmd       = slave_mcmd;
  end

  always_comb begin
    slave_sdata_accept  = u_request_vaid_accept_selector.mux(i_write_data_select, master_sdata_accept);
    master_mdata_valid  = u_request_vaid_accept_selector.demux(i_write_data_select, slave_mdata_valid);
    master_mdata        = slave_mdata;
  end

  always_comb begin
    master_mresp_accept = u_response_vaid_accept_selector.demux(i_response_select, slave_mresp_accept);
    slave_sresp_valid   = u_response_vaid_accept_selector.mux(i_response_select, master_sresp_valid);
    slave_sresp         = u_response_selector.mux(i_response_select, master_sresp);
  end

  for (genvar i = 0;i < MASTERS;++i) begin : g_master
    pzcorebus_if_unpacker #(BUS_CONFIG) u_unpacker (
      .corebus_if     (master_if[i]           ),
      .i_mcmd_valid   (master_mcmd_valid[i]   ),
      .o_scmd_accept  (master_scmd_accept[i]  ),
      .i_mcmd         (master_mcmd            ),
      .i_mdata_valid  (master_mdata_valid[i]  ),
      .o_sdata_accept (master_sdata_accept[i] ),
      .i_mdata        (master_mdata           ),
      .o_sresp_valid  (master_sresp_valid[i]  ),
      .i_mresp_accept (master_mresp_accept[i] ),
      .o_sresp        (master_sresp[i]        )
    );
  end
endmodule
