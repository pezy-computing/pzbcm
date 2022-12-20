//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_request_mux
  import  pzcorebus_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config    BUS_CONFIG    = '0,
  parameter int                 SLAVES        = 2,
  parameter pzbcm_selector_type SELECTOR_TYPE = PZBCM_SELECTOR_ONEHOT,
  parameter int                 SELECT_WIDTH  = calc_select_width(SELECTOR_TYPE, SLAVES)
)(
  input var [SELECT_WIDTH-1:0]  i_command_select,
  input var [SELECT_WIDTH-1:0]  i_write_data_select,
  interface.request_slave       slave_if[SLAVES],
  interface.request_master      master_if
);
  typedef logic [get_packed_command_width(BUS_CONFIG)-1:0]        pzcorebus_packed_command;
  typedef logic [get_packed_write_data_width(BUS_CONFIG, 1)-1:0]  pzcorebus_packed_write_data;

  logic [SLAVES-1:0]                        slave_mcmd_valid;
  logic [SLAVES-1:0]                        slave_scmd_accept;
  pzcorebus_packed_command  [SLAVES-1:0]    slave_mcmd;
  logic [SLAVES-1:0]                        slave_mdata_valid;
  logic [SLAVES-1:0]                        slave_sdata_accept;
  pzcorebus_packed_write_data [SLAVES-1:0]  slave_mdata;
  logic                                     master_mcmd_valid;
  logic                                     master_scmd_accept;
  pzcorebus_packed_command                  master_mcmd;
  logic                                     master_mdata_valid;
  logic                                     master_sdata_accept;
  pzcorebus_packed_write_data               master_mdata;

  pzbcm_selector #(
    .WIDTH          (1              ),
    .ENTRIES        (SLAVES         ),
    .SELECTOR_TYPE  (SELECTOR_TYPE  )
  ) u_request_valid_accept_selector();

  pzbcm_selector #(
    .TYPE           (pzcorebus_packed_command ),
    .ENTRIES        (SLAVES                   ),
    .SELECTOR_TYPE  (SELECTOR_TYPE            )
  ) u_command_selector();

  pzbcm_selector #(
    .TYPE           (pzcorebus_packed_write_data  ),
    .ENTRIES        (SLAVES                       ),
    .SELECTOR_TYPE  (SELECTOR_TYPE                )
  ) u_write_data_selector();

  pzcorebus_request_array_if_packer #(
    .BUS_CONFIG (BUS_CONFIG ),
    .SIZE       (SLAVES     )
  ) u_packer (
    .corebus_if     (slave_if           ),
    .o_mcmd_valid   (slave_mcmd_valid   ),
    .i_scmd_accept  (slave_scmd_accept  ),
    .o_mcmd         (slave_mcmd         ),
    .o_mdata_valid  (slave_mdata_valid  ),
    .i_sdata_accept (slave_sdata_accept ),
    .o_mdata        (slave_mdata        )
  );

  always_comb begin
    slave_scmd_accept = u_request_valid_accept_selector.demux(i_command_select, master_scmd_accept);
    master_mcmd_valid = u_request_valid_accept_selector.mux(i_command_select, slave_mcmd_valid);
    master_mcmd       = u_command_selector.mux(i_command_select, slave_mcmd);
  end

  always_comb begin
    slave_sdata_accept  = u_request_valid_accept_selector.demux(i_write_data_select, master_sdata_accept);
    master_mdata_valid  = u_request_valid_accept_selector.mux(i_write_data_select, slave_mdata_valid);
    master_mdata        = u_write_data_selector.mux(i_write_data_select, slave_mdata);
  end

  pzcorebus_request_if_unpacker #(
    .BUS_CONFIG (BUS_CONFIG )
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
