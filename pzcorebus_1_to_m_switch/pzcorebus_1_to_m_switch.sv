//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_1_to_m_switch
  import  pzcorebus_pkg::*,
          pzbcm_arbiter_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config          BUS_CONFIG                    = '0,
  parameter int                       MASTERS                       = 2,
  parameter bit                       EXTERNAL_DECODE               = 0,
  parameter pzbcm_selector_type       SELECTOR_TYPE                 = PZBCM_SELECTOR_BINARY,
  parameter int                       SELECT_WIDTH                  = calc_select_width(SELECTOR_TYPE, MASTERS),
  parameter int                       SELECT_LSB                    = BUS_CONFIG.address_width - SELECT_WIDTH,
  parameter bit                       WAIT_FOR_DATA                 = 0,
  parameter bit [1:0]                 ENABLE_ARBITER                = 2'b01,
  parameter int                       PRIORITY_WIDTH                = 0,
  parameter int                       WEIGHT_WIDTH                  = 0,
  parameter pzbcm_arbiter_weight_list WEIGHT                        = '1,
  parameter bit                       ENABLE_BROADCAST              = 0,
  parameter int                       MAX_NON_POSTED_WRITE_REQUESTS = 8,
  parameter bit [1:0]                 SLAVE_FIFO                    = 0,
  parameter bit [1:0]                 MASTER_FIFO                   = 0,
  parameter int                       COMMAND_DEPTH                 = 2,
  parameter int                       DATA_DEPTH                    = 2,
  parameter int                       RESPONSE_DEPTH                = 2,
  parameter bit                       ALIGN_OUT                     = 0,
  parameter int                       MINFO_WIDTH                   = get_request_info_width(BUS_CONFIG, 1)
)(
  input   var                                 i_clk,
  input   var                                 i_rst_n,
  input   var pzbcm_arbiter_config            i_arbiter_config,
  output  var pzcorebus_command_type          o_mcmd,
  output  var [BUS_CONFIG.id_width-1:0]       o_mid,
  output  var [BUS_CONFIG.address_width-1:0]  o_maddr,
  output  var [MINFO_WIDTH-1:0]               o_minfo,
  input   var [SELECT_WIDTH-1:0]              i_select,
  pzcorebus_if.slave                          slave_if,
  pzcorebus_if.master                         master_if[MASTERS]
);
  pzcorebus_if #(BUS_CONFIG)  bus_if[1+MASTERS]();

  if (ENABLE_BROADCAST && (BUS_CONFIG.profile == PZCOREBUS_CSR)) begin : g
    pzcorebus_1_to_m_switch_response_filter #(
      .BUS_CONFIG                     (BUS_CONFIG                     ),
      .MASTERS                        (MASTERS                        ),
      .MAX_NON_POSTED_WRITE_REQUESTS  (MAX_NON_POSTED_WRITE_REQUESTS  ),
      .SLAVE_FIFO                     (SLAVE_FIFO                     ),
      .COMMAND_DEPTH                  (COMMAND_DEPTH                  ),
      .RESPONSE_DEPTH                 (RESPONSE_DEPTH                 )
    ) u_response_filter (
      .i_clk      (i_clk      ),
      .i_rst_n    (i_rst_n    ),
      .slave_if   (slave_if   ),
      .master_if  (bus_if[0]  )
    );
  end
  else begin : g
    pzcorebus_fifo #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .COMMAND_DEPTH  (COMMAND_DEPTH  ),
      .COMMAND_VALID  (SLAVE_FIFO[0]  ),
      .DATA_DEPTH     (DATA_DEPTH     ),
      .DATA_VALID     (SLAVE_FIFO[0]  ),
      .RESPONSE_DEPTH (RESPONSE_DEPTH ),
      .RESPONSE_VALID (SLAVE_FIFO[1]  )
    ) u_slave_fifo (
      .i_clk          (i_clk      ),
      .i_rst_n        (i_rst_n    ),
      .i_clear        ('0         ),
      .o_empty        (),
      .o_almost_full  (),
      .o_full         (),
      .slave_if       (slave_if   ),
      .master_if      (bus_if[0]  )
    );
  end

  pzcorebus_request_1_to_m_switch #(
    .BUS_CONFIG       (BUS_CONFIG       ),
    .MASTERS          (MASTERS          ),
    .EXTERNAL_DECODE  (EXTERNAL_DECODE  ),
    .SELECTOR_TYPE    (SELECTOR_TYPE    ),
    .SELECT_WIDTH     (SELECT_WIDTH     ),
    .SELECT_LSB       (SELECT_LSB       ),
    .ENABLE_BROADCAST (ENABLE_BROADCAST ),
    .WAIT_FOR_DATA    (WAIT_FOR_DATA    ),
    .SLAVE_FIFO       ('0               ),
    .MASTER_FIFO      (MASTER_FIFO[0]   ),
    .COMMAND_DEPTH    (COMMAND_DEPTH    ),
    .DATA_DEPTH       (DATA_DEPTH       ),
    .ALIGN_OUT        (ALIGN_OUT        )
  ) u_request_switch (
    .i_clk      (i_clk              ),
    .i_rst_n    (i_rst_n            ),
    .o_mcmd     (o_mcmd             ),
    .o_mid      (o_mid              ),
    .o_maddr    (o_maddr            ),
    .o_minfo    (o_minfo            ),
    .i_select   (i_select           ),
    .slave_if   (bus_if[0]          ),
    .master_if  (bus_if[1:MASTERS]  )
  );

  pzcorebus_response_1_to_m_switch #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .MASTERS        (MASTERS        ),
    .ENABLE_ARBITER (ENABLE_ARBITER ),
    .PRIORITY_WIDTH (PRIORITY_WIDTH ),
    .WEIGHT_WIDTH   (WEIGHT_WIDTH   ),
    .WEIGHT         (WEIGHT         ),
    .SLAVE_FIFO     ('0             ),
    .MASTER_FIFO    (MASTER_FIFO[1] ),
    .RESPONSE_DEPTH (RESPONSE_DEPTH )
  ) u_response_switch (
    .i_clk            (i_clk              ),
    .i_rst_n          (i_rst_n            ),
    .i_arbiter_config (i_arbiter_config   ),
    .slave_if         (bus_if[0]          ),
    .master_if        (bus_if[1:MASTERS]  )
  );

  pzcorebus_array_connector #(MASTERS) u_master_connector (
    .slave_if   (bus_if[1:MASTERS]  ),
    .master_if  (master_if          )
  );
endmodule
