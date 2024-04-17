//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_request_xbar_switch
  import  pzcorebus_pkg::*,
          pzbcm_arbiter_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config          BUS_CONFIG          = '0,
  parameter int                       SLAVES              = 2,
  parameter int                       MASTERS             = 2,
  parameter bit                       EXTERNAL_DECODE     = 0,
  parameter pzbcm_selector_type       SELECTOR_TYPE       = PZBCM_SELECTOR_BINARY,
  parameter int                       SELECT_WIDTH        = calc_select_width(SELECTOR_TYPE, MASTERS),
  parameter int                       SELECT_LSB          = BUS_CONFIG.address_width - SELECT_WIDTH,
  parameter bit [1:0]                 ENABLE_ARBITER      = 2'b01,
  parameter int                       PRIORITY_WIDTH      = 0,
  parameter int                       WEIGHT_WIDTH        = 0,
  parameter pzbcm_arbiter_weight_list WEIGHT              = '1,
  parameter bit                       WAIT_FOR_DATA       = 0,
  parameter bit                       WAIT_FOR_DATA_LAST  = 0,
  parameter bit                       ENABLE_BROADCAST    = 0,
  parameter bit                       SLAVE_FIFO          = 0,
  parameter bit                       MASTER_FIFO         = 0,
  parameter int                       COMMAND_DEPTH       = 2,
  parameter int                       DATA_DEPTH          = 2,
  parameter bit                       ALIGN_OUT           = 0,
  parameter bit                       SVA_CHECKER         = 1
)(
  input   var                                 i_clk,
  input   var                                 i_rst_n,
  output  var pzcorebus_command [SLAVES-1:0]  o_mcmd,
  input   var [SLAVES-1:0][SELECT_WIDTH-1:0]  i_select,
  input   var pzbcm_arbiter_config            i_arbiter_config,
  interface.request_slave                     slave_if[SLAVES],
  interface.request_master                    master_if[MASTERS]
);
  localparam  int TOTAL = SLAVES * MASTERS;

  pzcorebus_request_if #(BUS_CONFIG)  slave_switch_if[TOTAL]();
  pzcorebus_request_if #(BUS_CONFIG)  master_switch_if[TOTAL]();

  for (genvar i = 0;i < SLAVES;++i) begin : g_slave_switch
    pzcorebus_request_1_to_m_switch #(
      .BUS_CONFIG         (BUS_CONFIG         ),
      .MASTERS            (MASTERS            ),
      .EXTERNAL_DECODE    (EXTERNAL_DECODE    ),
      .SELECTOR_TYPE      (SELECTOR_TYPE      ),
      .SELECT_WIDTH       (SELECT_WIDTH       ),
      .SELECT_LSB         (SELECT_LSB         ),
      .WAIT_FOR_DATA      (WAIT_FOR_DATA      ),
      .WAIT_FOR_DATA_LAST (WAIT_FOR_DATA_LAST ),
      .ENABLE_BROADCAST   (ENABLE_BROADCAST   ),
      .SLAVE_FIFO         (SLAVE_FIFO         ),
      .MASTER_FIFO        (0                  ),
      .COMMAND_DEPTH      (COMMAND_DEPTH      ),
      .DATA_DEPTH         (DATA_DEPTH         ),
      .SVA_CHECKER        (SVA_CHECKER        )
    ) u_switch (
      .i_clk      (i_clk                                ),
      .i_rst_n    (i_rst_n                              ),
      .o_mcmd     (o_mcmd[i]                            ),
      .i_select   (i_select[i]                          ),
      .slave_if   (slave_if[i]                          ),
      .master_if  (master_if[MASTERS*i:MASTERS*(i+1)-1] )
    );
  end

  pzcorebus_request_transposer #(
    .M  (SLAVES   ),
    .N  (MASTERS  )
  ) u_transposer (
    .slave_if   (slave_switch_if  ),
    .master_if  (master_switch_if )
  );

  for (genvar i = 0;i < MASTERS;++i) begin : g_master_switch
    pzcorebus_request_m_to_1_switch #(
      .BUS_CONFIG         (BUS_CONFIG     ),
      .SLAVES             (SLAVES         ),
      .ENABLE_ARBITER     (ENABLE_ARBITER ),
      .PRIORITY_WIDTH     (PRIORITY_WIDTH ),
      .WEIGHT_WIDTH       (WEIGHT_WIDTH   ),
      .WEIGHT             (WEIGHT         ),
      .WAIT_FOR_DATA      (0              ),
      .WAIT_FOR_RESPONSE  (0              ),
      .SLAVE_FIFO         (0              ),
      .MASTER_FIFO        (MASTER_FIFO    ),
      .COMMAND_DEPTH      (COMMAND_DEPTH  ),
      .DATA_DEPTH         (DATA_DEPTH     ),
      .ALIGN_OUT          (ALIGN_OUT      ),
      .SVA_CHECKER        (0              )
    ) u_switch (
      .i_clk              (i_clk                                    ),
      .i_rst_n            (i_rst_n                                  ),
      .i_arbiter_config   (i_arbiter_config                         ),
      .o_response_select  (),
      .i_response_ack     ('0                                       ),
      .slave_if           (master_switch_if[SLAVES:SLAVES*(i+1)-1]  ),
      .master_if          (master_if[i]                             )
    );
  end
endmodule
