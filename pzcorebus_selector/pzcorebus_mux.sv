//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_mux
  import  pzcorebus_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config    BUS_CONFIG              = '0,
  parameter int                 SLAVES                  = 2,
  parameter pzbcm_selector_type SELECTOR_TYPE           = PZBCM_SELECTOR_ONEHOT,
  parameter pzbcm_selector_type REQUEST_SELECTOR_TYPE   = SELECTOR_TYPE,
  parameter pzbcm_selector_type RESPONSE_SELECTOR_TYPE  = SELECTOR_TYPE,
  parameter int                 REQUEST_SELECT_WIDTH    = calc_select_width(REQUEST_SELECTOR_TYPE, SLAVES),
  parameter int                 RESPONSE_SELECT_WIDTH   = calc_select_width(RESPONSE_SELECTOR_TYPE, SLAVES)
)(
  input var [REQUEST_SELECT_WIDTH-1:0]  i_command_select,
  input var [REQUEST_SELECT_WIDTH-1:0]  i_write_data_select,
  input var [RESPONSE_SELECT_WIDTH-1:0] i_response_select,
  pzcorebus_if.slave                    slave_if[SLAVES],
  pzcorebus_if.master                   master_if
);
  typedef logic [get_packed_command_width(BUS_CONFIG)-1:0]        pzcorebus_packed_command;
  typedef logic [get_packed_write_data_width(BUS_CONFIG, 1)-1:0]  pzcorebus_packed_write_data;
  typedef logic [get_packed_response_width(BUS_CONFIG)-1:0]       pzcorebus_packed_response;

  logic [SLAVES-1:0]                        slave_mcmd_valid;
  logic [SLAVES-1:0]                        slave_scmd_accept;
  pzcorebus_packed_command  [SLAVES-1:0]    slave_mcmd;
  logic [SLAVES-1:0]                        slave_mdata_valid;
  logic [SLAVES-1:0]                        slave_sdata_accept;
  pzcorebus_packed_write_data [SLAVES-1:0]  slave_mdata;
  logic [SLAVES-1:0]                        slave_sresp_valid;
  logic [SLAVES-1:0]                        slave_mresp_accept;
  pzcorebus_packed_response                 slave_sresp;
  logic                                     master_mcmd_valid;
  logic                                     master_scmd_accept;
  pzcorebus_packed_command                  master_mcmd;
  logic                                     master_mdata_valid;
  logic                                     master_sdata_accept;
  pzcorebus_packed_write_data               master_mdata;
  logic                                     master_sresp_valid;
  logic                                     master_mresp_accept;
  pzcorebus_packed_response                 master_sresp;

  pzbcm_selector #(
    .WIDTH          (1                      ),
    .ENTRIES        (SLAVES                 ),
    .SELECTOR_TYPE  (REQUEST_SELECTOR_TYPE  )
  ) u_request_valid_accept_selector();

  pzbcm_selector #(
    .TYPE           (pzcorebus_packed_command ),
    .ENTRIES        (SLAVES                   ),
    .SELECTOR_TYPE  (REQUEST_SELECTOR_TYPE    )
  ) u_command_selector();

  pzbcm_selector #(
    .TYPE           (pzcorebus_packed_write_data  ),
    .ENTRIES        (SLAVES                       ),
    .SELECTOR_TYPE  (REQUEST_SELECTOR_TYPE        )
  ) u_write_data_selector();

  pzbcm_selector #(
    .WIDTH          (1                      ),
    .ENTRIES        (SLAVES                 ),
    .SELECTOR_TYPE  (RESPONSE_SELECTOR_TYPE )
  ) u_response_valid_accept_selector();

  for (genvar i = 0;i < SLAVES;++i) begin : g_slave
    pzcorebus_if_packer #(BUS_CONFIG) u_packer (
      .corebus_if     (slave_if[i]            ),
      .o_mcmd_valid   (slave_mcmd_valid[i]    ),
      .i_scmd_accept  (slave_scmd_accept[i]   ),
      .o_mcmd         (slave_mcmd[i]          ),
      .o_mdata_valid  (slave_mdata_valid[i]   ),
      .i_sdata_accept (slave_sdata_accept[i]  ),
      .o_mdata        (slave_mdata[i]         ),
      .i_sresp_valid  (slave_sresp_valid[i]   ),
      .o_mresp_accept (slave_mresp_accept[i]  ),
      .i_sresp        (slave_sresp            )
    );
  end

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

  always_comb begin
    master_mresp_accept = u_response_valid_accept_selector.mux(i_response_select, slave_mresp_accept);
    slave_sresp_valid   = u_response_valid_accept_selector.demux(i_response_select, master_sresp_valid);
    slave_sresp         = master_sresp;
  end

  pzcorebus_if_unpacker #(BUS_CONFIG) u_unpacker (
    .corebus_if     (master_if            ),
    .i_mcmd_valid   (master_mcmd_valid    ),
    .o_scmd_accept  (master_scmd_accept   ),
    .i_mcmd         (master_mcmd          ),
    .i_mdata_valid  (master_mdata_valid   ),
    .o_sdata_accept (master_sdata_accept  ),
    .i_mdata        (master_mdata         ),
    .o_sresp_valid  (master_sresp_valid   ),
    .i_mresp_accept (master_mresp_accept  ),
    .o_sresp        (master_sresp         )
  );
endmodule
