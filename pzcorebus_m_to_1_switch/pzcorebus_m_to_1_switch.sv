//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_m_to_1_switch
  import  pzcorebus_pkg::*,
          pzbcm_arbiter_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config          BUS_CONFIG            = '0,
  parameter int                       SLAVES                = 2,
  parameter bit                       EXTERNAL_DECODE       = 0,
  parameter bit                       WAIT_FOR_DATA         = 0,
  parameter bit                       WAIT_FOR_RESPONSE     = 0,
  parameter pzbcm_selector_type       SELECTOR_TYPE         = PZBCM_SELECTOR_BINARY,
  parameter int                       SELECT_WIDTH          = calc_select_width(SELECTOR_TYPE, SLAVES),
  parameter int                       SELECT_LSB            = BUS_CONFIG.id_width - SELECT_WIDTH,
  parameter bit [1:0]                 ENABLE_ARBITER        = 2'b01,
  parameter int                       PRIORITY_WIDTH        = 0,
  parameter int                       WEIGHT_WIDTH          = 0,
  parameter pzbcm_arbiter_weight_list WEIGHT                = '1,
  parameter bit [1:0]                 SLAVE_FIFO            = '0,
  parameter bit [1:0]                 MASTER_FIFO           = '0,
  parameter int                       COMMAND_DEPTH         = 2,
  parameter int                       DATA_DEPTH            = 2,
  parameter int                       RESPONSE_DEPTH        = 2,
  parameter bit                       ALIGN_OUT             = 0,
  parameter bit                       SVA_CHECKER           = 1,
  parameter bit                       REQUEST_SVA_CHECKER   = SVA_CHECKER,
  parameter bit                       RESPONSE_SVA_CHECKER  = SVA_CHECKER
)(
  input   var                           i_clk,
  input   var                           i_rst_n,
  input   var pzbcm_arbiter_config      i_arbiter_config,
  output  var [BUS_CONFIG.id_width-1:0] o_sid,
  input   var [SELECT_WIDTH-1:0]        i_select,
  pzcorebus_if.slave                    slave_if[SLAVES],
  pzcorebus_if.master                   master_if
);
  localparam  pzbcm_selector_type RESPONSE_SELECT_TYPE  = (WAIT_FOR_RESPONSE) ? PZBCM_SELECTOR_ONEHOT : SELECTOR_TYPE;
  localparam  int                 RESPONSE_SELECT_WIDTH = (WAIT_FOR_RESPONSE) ? SLAVES                : SELECT_WIDTH;

  pzcorebus_if #(BUS_CONFIG)        bus_if[SLAVES+1]();
  logic                             response_ack;
  logic [SLAVES-1:0]                response_select;
  logic [RESPONSE_SELECT_WIDTH-1:0] select;

  pzcorebus_array_connector #(SLAVES) u_slave_connector (
    .slave_if   (slave_if           ),
    .master_if  (bus_if[0:SLAVES-1] )
  );

  pzcorebus_request_m_to_1_switch #(
    .BUS_CONFIG         (BUS_CONFIG           ),
    .SLAVES             (SLAVES               ),
    .ENABLE_ARBITER     (ENABLE_ARBITER       ),
    .PRIORITY_WIDTH     (PRIORITY_WIDTH       ),
    .WEIGHT_WIDTH       (WEIGHT_WIDTH         ),
    .WEIGHT             (WEIGHT               ),
    .WAIT_FOR_DATA      (WAIT_FOR_DATA        ),
    .WAIT_FOR_RESPONSE  (WAIT_FOR_RESPONSE    ),
    .SLAVE_FIFO         (SLAVE_FIFO[0]        ),
    .MASTER_FIFO        (MASTER_FIFO[0]       ),
    .COMMAND_DEPTH      (COMMAND_DEPTH        ),
    .DATA_DEPTH         (DATA_DEPTH           ),
    .ALIGN_OUT          (ALIGN_OUT            ),
    .SVA_CHECKER        (REQUEST_SVA_CHECKER  )
  ) u_request_switch (
    .i_clk              (i_clk              ),
    .i_rst_n            (i_rst_n            ),
    .i_arbiter_config   (i_arbiter_config   ),
    .o_response_select  (response_select    ),
    .i_response_ack     (response_ack       ),
    .slave_if           (bus_if[0:SLAVES-1] ),
    .master_if          (bus_if[SLAVES]     )
  );

  pzcorebus_response_m_to_1_switch #(
    .BUS_CONFIG       (BUS_CONFIG                           ),
    .SLAVES           (SLAVES                               ),
    .EXTERNAL_DECODE  (EXTERNAL_DECODE || WAIT_FOR_RESPONSE ),
    .SELECTOR_TYPE    (RESPONSE_SELECT_TYPE                 ),
    .SELECT_WIDTH     (RESPONSE_SELECT_WIDTH                ),
    .SELECT_LSB       (SELECT_LSB                           ),
    .SLAVE_FIFO       (SLAVE_FIFO[1]                        ),
    .MASTER_FIFO      (MASTER_FIFO[1]                       ),
    .RESPONSE_DEPTH   (RESPONSE_DEPTH                       ),
    .SVA_CHECKER      (RESPONSE_SVA_CHECKER                 )
  ) u_response_switch (
    .i_clk          (i_clk              ),
    .i_rst_n        (i_rst_n            ),
    .o_sid          (o_sid              ),
    .i_select       (select             ),
    .o_response_ack (response_ack       ),
    .slave_if       (bus_if[0:SLAVES-1] ),
    .master_if      (bus_if[SLAVES]     )
  );

  always_comb begin
    if (WAIT_FOR_RESPONSE) begin
      select  = RESPONSE_SELECT_WIDTH'(response_select);
    end
    else begin
      select  = RESPONSE_SELECT_WIDTH'(i_select);
    end
  end

  pzcorebus_connector u_master_connector (
    .slave_if   (bus_if[SLAVES] ),
    .master_if  (master_if      )
  );
endmodule
