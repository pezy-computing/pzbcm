//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_response_mux
  import  pzcorebus_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config    BUS_CONFIG    = '0,
  parameter int                 SLAVES        = 2,
  parameter pzbcm_selector_type SELECTOR_TYPE = PZBCM_SELECTOR_ONEHOT,
  parameter int                 SELECT_WIDTH  = calc_select_width(SELECTOR_TYPE, SLAVES)
)(
  input var [SELECT_WIDTH-1:0]  i_response_select,
  interface.response_slave      slave_if[SLAVES],
  interface.response_master     master_if
);
  typedef logic [get_packed_response_width(BUS_CONFIG)-1:0] pzcorebus_packed_response;

  logic [SLAVES-1:0]                      slave_sresp_valid;
  logic [SLAVES-1:0]                      slave_mresp_accept;
  pzcorebus_packed_response [SLAVES-1:0]  slave_sresp;
  logic                                   master_sresp_valid;
  logic                                   master_mresp_accept;
  pzcorebus_packed_response               master_sresp;

  pzbcm_selector #(
    .WIDTH          (1              ),
    .ENTRIES        (SLAVES         ),
    .SELECTOR_TYPE  (SELECTOR_TYPE  )
  ) u_response_valid_accept_selector();

  pzcorebus_response_array_if_packer #(
    .BUS_CONFIG (BUS_CONFIG ),
    .SIZE       (SLAVES     )
  ) u_packer (
    .corebus_if     (slave_if ),
    .i_sresp_valid  (slave_sresp_valid  ),
    .o_mresp_accept (slave_mresp_accept ),
    .i_sresp        (slave_sresp        )
  );

  always_comb begin
    master_mresp_accept = u_response_valid_accept_selector.mux(i_response_select, slave_mresp_accept);
    slave_sresp_valid   = u_response_valid_accept_selector.demux(i_response_select, master_sresp_valid);
    for (int i = 0;i < SLAVES;++i) begin
      slave_sresp[i]  = master_sresp;
    end
  end

  pzcorebus_response_if_unpacker #(BUS_CONFIG) u_unpacker (
    .corebus_if     (master_if            ),
    .o_sresp_valid  (master_sresp_valid   ),
    .i_mresp_accept (master_mresp_accept  ),
    .o_sresp        (master_sresp         )
  );
endmodule
