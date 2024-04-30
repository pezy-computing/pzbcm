//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_xbar_switch
  import  pzcorebus_pkg::*,
          pzbcm_arbiter_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config          BUS_CONFIG                = 0,
  parameter int                       SLAVES                    = 2,
  parameter int                       MASTERS                   = 2,
  parameter bit                       EXTERNAL_DECODE           = 0,
  parameter pzbcm_selector_type       SELECTOR_TYPE             = PZBCM_SELECTOR_BINARY,
  parameter bit                       REQUEST_EXTERNAL_DECODE   = EXTERNAL_DECODE,
  parameter pzbcm_selector_type       REQUEST_SELECTOR_TYPE     = SELECTOR_TYPE,
  parameter int                       REQUEST_SELECT_WIDTH      = calc_select_width(REQUEST_SELECTOR_TYPE, MASTERS),
  parameter int                       REQUEST_SELECT_LSB        = BUS_CONFIG.address_width - REQUEST_SELECT_WIDTH,
  parameter bit                       RESPONSE_EXTERNAL_DECODE  = EXTERNAL_DECODE,
  parameter pzbcm_selector_type       RESPONSE_SELECTOR_TYPE    = SELECTOR_TYPE,
  parameter int                       RESPONSE_SELECT_WIDTH     = calc_select_width(RESPONSE_SELECTOR_TYPE, SLAVES),
  parameter int                       RESPONSE_SELECT_LSB       = BUS_CONFIG.id_width - RESPONSE_SELECT_WIDTH,
  parameter bit [1:0]                 ENABLE_ARBITER            = 2'b01,
  parameter bit [1:0]                 REQUEST_ENABLE_ARBITER    = ENABLE_ARBITER,
  parameter int                       REQUEST_PRIORITY_WIDTH    = 0,
  parameter int                       REQUEST_WEIGHT_WIDTH      = 0,
  parameter pzbcm_arbiter_weight_list REQUEST_WEIGHT            = '1,
  parameter bit [1:0]                 RESPONSE_ENABLE_ARBITER   = ENABLE_ARBITER,
  parameter int                       RESPONSE_PRIORITY_WIDTH   = 0,
  parameter int                       RESPONSE_WEIGHT_WIDTH     = 0,
  parameter pzbcm_arbiter_weight_list RESPONSE_WEIGHT           = '1,
  parameter bit                       WAIT_FOR_DATA             = 0,
  parameter bit                       WAIT_FOR_DATA_LAST        = 0,
  parameter bit                       ENABLE_BROADCAST          = 0,
  parameter bit                       ALIGN_OUT                 = 0,
  parameter bit [1:0]                 SLAVE_FIFO                = '0,
  parameter bit [1:0]                 MASTER_FIFO               = '0,
  parameter int                       COMMAND_DEPTH             = 2,
  parameter int                       DATA_DEPTH                = 2,
  parameter int                       RESPONSE_DEPTH            = 2,
  parameter bit                       SVA_CHECKER               = 1,
  parameter bit                       REQUEST_SVA_CHECKER       = SVA_CHECKER,
  parameter bit                       RESPONSE_SVA_CHECKER      = SVA_CHECKER
)(
  input   var                                           i_clk,
  input   var                                           i_rst_n,
  output  var pzcorebus_command [SLAVES-1:0]            o_mcmd,
  input   var [SLAVES-1:0][REQUEST_SELECT_WIDTH-1:0]    i_request_select,
  input   var pzbcm_arbiter_config                      i_request_arbiter_config,
  output  var pzcorebus_response  [MASTERS-1:0]         o_sresp,
  input   var [MASTERS-1:0][RESPONSE_SELECT_WIDTH-1:0]  i_response_select,
  input   var pzbcm_arbiter_config                      i_response_arbiter_config,
  pzcorebus_if.slave                                    slave_if[SLAVES],
  pzcorebus_if.master                                   master_if[MASTERS]
);
  pzcorebus_if #(BUS_CONFIG)  slave_bus_if[SLAVES]();
  pzcorebus_if #(BUS_CONFIG)  master_bus_if[MASTERS]();

  pzcorebus_array_connector #(
    .N  (SLAVES )
  ) u_slave_connector (
    .slave_if   (slave_if     ),
    .master_if  (slave_bus_if )
  );

  pzcorebus_request_xbar_switch #(
    .BUS_CONFIG         (BUS_CONFIG               ),
    .SLAVES             (SLAVES                   ),
    .MASTERS            (MASTERS                  ),
    .EXTERNAL_DECODE    (REQUEST_EXTERNAL_DECODE  ),
    .SELECTOR_TYPE      (REQUEST_SELECTOR_TYPE    ),
    .SELECT_WIDTH       (REQUEST_SELECT_WIDTH     ),
    .SELECT_LSB         (REQUEST_SELECT_LSB       ),
    .ENABLE_ARBITER     (REQUEST_ENABLE_ARBITER   ),
    .PRIORITY_WIDTH     (REQUEST_PRIORITY_WIDTH   ),
    .WEIGHT_WIDTH       (REQUEST_WEIGHT_WIDTH     ),
    .WEIGHT             (REQUEST_WEIGHT           ),
    .WAIT_FOR_DATA      (WAIT_FOR_DATA            ),
    .WAIT_FOR_DATA_LAST (WAIT_FOR_DATA_LAST       ),
    .ENABLE_BROADCAST   (ENABLE_BROADCAST         ),
    .SLAVE_FIFO         (SLAVE_FIFO[0]            ),
    .MASTER_FIFO        (MASTER_FIFO[0]           ),
    .COMMAND_DEPTH      (COMMAND_DEPTH            ),
    .DATA_DEPTH         (DATA_DEPTH               ),
    .ALIGN_OUT          (ALIGN_OUT                ),
    .SVA_CHECKER        (REQUEST_SVA_CHECKER      )
  ) u_request_xbar_switch (
      .i_clk            (i_clk                    ),
      .i_rst_n          (i_rst_n                  ),
      .o_mcmd           (o_mcmd                   ),
      .i_select         (i_request_select         ),
      .i_arbiter_config (i_request_arbiter_config ),
      .slave_if         (slave_bus_if             ),
      .master_if        (master_bus_if            )
  );

  pzcorebus_response_xbar_switch #(
    .BUS_CONFIG       (BUS_CONFIG               ),
    .SLAVES           (SLAVES                   ),
    .MASTERS          (MASTERS                  ),
    .ENABLE_ARBITER   (RESPONSE_ENABLE_ARBITER  ),
    .PRIORITY_WIDTH   (RESPONSE_PRIORITY_WIDTH  ),
    .WEIGHT_WIDTH     (RESPONSE_WEIGHT_WIDTH    ),
    .WEIGHT           (RESPONSE_WEIGHT          ),
    .EXTERNAL_DECODE  (RESPONSE_EXTERNAL_DECODE ),
    .SELECTOR_TYPE    (RESPONSE_SELECTOR_TYPE   ),
    .SELECT_WIDTH     (RESPONSE_SELECT_WIDTH    ),
    .SELECT_LSB       (RESPONSE_SELECT_LSB      ),
    .SLAVE_FIFO       (SLAVE_FIFO[1]            ),
    .MASTER_FIFO      (MASTER_FIFO[1]           ),
    .RESPONSE_DEPTH   (RESPONSE_DEPTH           ),
    .SVA_CHECKER      (RESPONSE_SVA_CHECKER     )
  ) u_response_xbar_switch (
    .i_clk            (i_clk                      ),
    .i_rst_n          (i_rst_n                    ),
    .i_arbiter_config (i_response_arbiter_config  ),
    .o_sresp          (o_sresp                    ),
    .i_select         (i_response_select          ),
    .slave_if         (slave_bus_if               ),
    .master_if        (master_bus_if              )
  );

  pzcorebus_array_connector #(
    .N  (MASTERS  )
  ) u_master_connector (
    .slave_if   (master_bus_if  ),
    .master_if  (master_if      )
  );
endmodule
