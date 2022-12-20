//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_request_demux
  import  pzcorebus_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config    BUS_CONFIG    = '0,
  parameter int                 MASTERS       = 2,
  parameter pzbcm_selector_type SELECTOR_TYPE = PZBCM_SELECTOR_ONEHOT,
  parameter int                 SELECT_WIDTH  = calc_select_width(SELECTOR_TYPE, MASTERS)
)(
  input var [SELECT_WIDTH-1:0]  i_command_select,
  input var [SELECT_WIDTH-1:0]  i_write_data_select,
  interface.request_slave       slave_if,
  interface.request_master      master_if[MASTERS]
);
  typedef logic [get_packed_command_width(BUS_CONFIG)-1:0]        pzcorebus_packed_command;
  typedef logic [get_packed_write_data_width(BUS_CONFIG, 1)-1:0]  pzcorebus_packed_write_data;

  logic                                     slave_mcmd_valid;
  logic                                     slave_scmd_accept;
  pzcorebus_packed_command                  slave_mcmd;
  logic                                     slave_mdata_valid;
  logic                                     slave_sdata_accept;
  pzcorebus_packed_write_data               slave_mdata;
  logic [MASTERS-1:0]                       master_mcmd_valid;
  logic [MASTERS-1:0]                       master_scmd_accept;
  pzcorebus_packed_command  [MASTERS-1:0]   master_mcmd;
  logic [MASTERS-1:0]                       master_mdata_valid;
  logic [MASTERS-1:0]                       master_sdata_accept;
  pzcorebus_packed_write_data [MASTERS-1:0] master_mdata;

  pzbcm_selector #(
    .WIDTH          (1              ),
    .ENTRIES        (MASTERS        ),
    .SELECTOR_TYPE  (SELECTOR_TYPE  )
  ) u_request_vaid_accept_selector();

  pzcorebus_response_if_packer #(BUS_CONFIG) u_packer (
    .corebus_if     (slave_if           ),
    .o_mcmd_valid   (slave_mcmd_valid   ),
    .i_scmd_accept  (slave_scmd_accept  ),
    .o_mcmd         (slave_mcmd         ),
    .o_mdata_valid  (slave_mdata_valid  ),
    .i_sdata_accept (slave_sdata_accept ),
    .o_mdata        (slave_mdata        )
  );

  always_comb begin
    slave_scmd_accept = u_request_vaid_accept_selector.mux(i_command_select, master_scmd_accept);
    master_mcmd_valid = u_request_vaid_accept_selector.demux(i_command_select, slave_mcmd_valid);
    for (int i = 0;i < MASTERS;++i) begin
      master_mcmd[i]  = slave_mcmd;
    end
  end

  always_comb begin
    slave_sdata_accept  = u_request_vaid_accept_selector.mux(i_write_data_select, master_sdata_accept);
    master_mdata_valid  = u_request_vaid_accept_selector.demux(i_write_data_select, slave_mdata_valid);
    for (int i = 0;i < MASTERS;++i) begin
      master_mdata[i] = slave_mdata;
    end
  end

  pzcorebus_request_array_if_unpacker #(
    .BUS_CONFIG (BUS_CONFIG ),
    .SIZE       (MASTERS    )
  ) u_unpacker (
    .corebus_if     (master_if            ),
    .i_mcmd_valid   (master_mcmd_valid    ),
    .o_scmd_accept  (master_scmd_accept   ),
    .i_mcmd         (master_mcmd          ),
    .i_mdata_valid  (master_mdata_valid   ),
    .o_sdata_accept (master_sdata_accept  ),
    .i_mdata        (master_mdata         )
  );
endmodule
