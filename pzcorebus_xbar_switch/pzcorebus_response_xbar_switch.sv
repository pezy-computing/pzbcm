//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_response_xbar_switch
  import  pzcorebus_pkg::*,
          pzbcm_arbiter_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config          BUS_CONFIG      = '0,
  parameter int                       SLAVES          = 2,
  parameter int                       MASTERS         = 2,
  parameter bit [1:0]                 ENABLE_ARBITER  = 2'b01,
  parameter int                       PRIORITY_WIDTH  = 0,
  parameter int                       WEIGHT_WIDTH    = 0,
  parameter pzbcm_arbiter_weight_list WEIGHT          = '1,
  parameter bit                       EXTERNAL_DECODE = 0,
  parameter pzbcm_selector_type       SELECTOR_TYPE   = PZBCM_SELECTOR_BINARY,
  parameter int                       SELECT_WIDTH    = calc_select_width(SELECTOR_TYPE, SLAVES),
  parameter int                       SELECT_LSB      = BUS_CONFIG.id_width - SELECT_WIDTH,
  parameter bit                       SLAVE_FIFO      = 0,
  parameter bit                       MASTER_FIFO     = 0,
  parameter int                       RESPONSE_DEPTH  = 2,
  parameter bit                       SVA_CHECKER     = 1
)(
  input   var                                         i_clk,
  input   var                                         i_rst_n,
  input   var pzbcm_arbiter_config                    i_arbiter_config,
  output  var [MASTERS-1:0][BUS_CONFIG.id_width-1:0]  o_sid,
  input   var [MASTERS-1:0][SELECT_WIDTH-1:0]         i_select,
  interface.response_slave                            slave_if[SLAVES],
  interface.response_master                           master_if[MASTERS]
);
  localparam  int TOTAL = SLAVES * MASTERS;

  pzcorebus_response_if #(BUS_CONFIG) slave_switch_if[TOTAL]();
  pzcorebus_response_if #(BUS_CONFIG) master_switch_if[TOTAL]();

  for (genvar i = 0;i < SLAVES;++i) begin : g_slave_switch
    pzcorebus_response_1_to_m_switch #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .MASTERS        (MASTERS        ),
      .ENABLE_ARBITER (ENABLE_ARBITER ),
      .PRIORITY_WIDTH (PRIORITY_WIDTH ),
      .WEIGHT_WIDTH   (WEIGHT_WIDTH   ),
      .WEIGHT         (WEIGHT         ),
      .SLAVE_FIFO     (SLAVE_FIFO     ),
      .MASTER_FIFO    (0              ),
      .RESPONSE_DEPTH (RESPONSE_DEPTH ),
      .SVA_CHECKER    (0              )
    ) u_switch (
      .i_clk            (i_clk                                      ),
      .i_rst_n          (i_rst_n                                    ),
      .i_arbiter_config (i_arbiter_config                           ),
      .slave_if         (slave_if[i]                                ),
      .master_if        (slave_switch_if[MASTERS*i:MASTERS*(i+1)-1] )
    );
  end

  pzcorebus_response_transposer #(
    .M  (SLAVES   ),
    .N  (MASTERS  )
  ) u_transposer (
    .slave_if   (slave_switch_if  ),
    .master_if  (master_switch_if )
  );

  for (genvar i = 0;i < MASTERS;++i) begin : g_master_switch
    pzcorebus_response_m_to_1_switch #(
      .BUS_CONFIG       (BUS_CONFIG       ),
      .SLAVES           (SLAVES           ),
      .EXTERNAL_DECODE  (EXTERNAL_DECODE  ),
      .SELECTOR_TYPE    (SELECTOR_TYPE    ),
      .SELECT_WIDTH     (SELECT_WIDTH     ),
      .SELECT_LSB       (SELECT_LSB       ),
      .SLAVE_FIFO       (0                ),
      .MASTER_FIFO      (MASTER_FIFO      ),
      .RESPONSE_DEPTH   (RESPONSE_DEPTH   ),
      .SVA_CHECKER      (SVA_CHECKER      )
    ) u_switch (
      .i_clk          (i_clk                                      ),
      .i_rst_n        (i_rst_n                                    ),
      .o_sid          (o_sid[i]                                   ),
      .i_select       (i_select[i]                                ),
      .o_response_ack (),
      .slave_if       (master_switch_if[SLAVES*i:SLAVES*(i+1)-1]  ),
      .master_if      (master_if[i]                               )
    );
  end
endmodule
