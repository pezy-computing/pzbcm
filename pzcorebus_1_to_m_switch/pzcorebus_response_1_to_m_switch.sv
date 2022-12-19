//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_response_1_to_m_switch
  import  pzcorebus_pkg::*,
          pzbcm_arbiter_pkg::*,
          pzbcm_selector_pkg::PZBCM_SELECTOR_ONEHOT;
#(
  parameter pzcorebus_config          BUS_CONFIG      = '0,
  parameter int                       MASTERS         = 2,
  parameter bit [1:0]                 ENABLE_ARBITER  = '1,
  parameter int                       PRIORITY_WIDTH  = 0,
  parameter int                       WEIGHT_WIDTH    = 0,
  parameter pzbcm_arbiter_weight_list WEIGHT          = '1,
  parameter bit                       SLAVE_FIFO      = 0,
  parameter bit                       MASTER_FIFO     = 0,
  parameter int                       RESPONSE_DEPTH  = 2
)(
  input var                       i_clk,
  input var                       i_rst_n,
  input var pzbcm_arbiter_config  i_arbiter_config,
  interface.response_slave        slave_if,
  interface.response_master       master_if[MASTERS]
);
  pzcorebus_response_if #(BUS_CONFIG) fifo_if();
  pzcorebus_response_if #(BUS_CONFIG) switch_if[MASTERS]();

//--------------------------------------------------------------
//  Slave FIFO
//--------------------------------------------------------------
  pzcorebus_response_fifo #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .RESPONSE_DEPTH (RESPONSE_DEPTH ),
    .RESPONSE_VALID (SLAVE_FIFO     )
  ) u_slave_fifo (
    .i_clk          (i_clk    ),
    .i_rst_n        (i_rst_n  ),
    .i_clear        ('0       ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (slave_if ),
    .master_if      (fifo_if  )
  );

//--------------------------------------------------------------
//  Switch
//--------------------------------------------------------------
  logic [MASTERS-1:0] response_valid;
  logic [MASTERS-1:0] response_grant;
  logic               response_free;

  for (genvar i = 0;i < MASTERS;++i) begin : g_response_valid
    always_comb begin
      response_valid[i] = switch_if[i].sresp_valid;
    end
  end

  always_comb begin
    response_free = fifo_if.response_last_burst_ack();
  end

  pzbcm_arbiter #(
    .REQUESTS       (MASTERS        ),
    .ENABLE_ARBITER (ENABLE_ARBITER ),
    .PRIORITY_WIDTH (PRIORITY_WIDTH ),
    .WEIGHT_WIDTH   (WEIGHT_WIDTH   ),
    .WEIGHT         (WEIGHT         ),
    .ONEHOT_GRANT   (1              ),
    .KEEP_RESULT    (1              )
  ) u_arbiter (
    .i_clk      (i_clk                    ),
    .i_rst_n    (i_rst_n                  ),
    .i_config   (i_arbiter_config         ),
    .i_request  (response_valid           ),
    .o_grant    (response_grant           ),
    .i_free     ({MASTERS{response_free}} )
  );

  pzcorebus_response_demux #(
    .BUS_CONFIG     (BUS_CONFIG             ),
    .MASTERS        (MASTERS                ),
    .SELECTOR_TYPE  (PZBCM_SELECTOR_ONEHOT  )
  ) u_selector (
    .i_response_select  (response_grant ),
    .slave_if           (fifo_if        ),
    .master_if          (switch_if      )
  );

//--------------------------------------------------------------
//  Master FIFO
//--------------------------------------------------------------
  for (genvar i = 0;i < MASTERS;++i) begin : g_master_fifo
    pzcorebus_response_fifo #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .RESPONSE_DEPTH (RESPONSE_DEPTH ),
      .RESPONSE_VALID (MASTER_FIFO    )
    ) u_master_fifo (
      .i_clk          (i_clk        ),
      .i_rst_n        (i_rst_n      ),
      .i_clear        ('0           ),
      .o_empty        (),
      .o_almost_full  (),
      .o_full         (),
      .slave_if       (switch_if[i] ),
      .master_if      (master_if[i] )
    );
  end
endmodule
