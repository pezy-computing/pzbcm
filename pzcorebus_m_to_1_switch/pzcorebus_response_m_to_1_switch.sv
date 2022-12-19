//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_response_m_to_1_switch
  import  pzcorebus_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config    BUS_CONFIG      = '0,
  parameter int                 SLAVES          = 2,
  parameter bit                 EXTERNAL_DECODE = 0,
  parameter pzbcm_selector_type SELECTOR_TYPE   = PZBCM_SELECTOR_BINARY,
  parameter int                 SELECT_WIDTH    = calc_select_width(SELECTOR_TYPE, SLAVES),
  parameter int                 SELECT_LSB      = BUS_CONFIG.id_width - SELECT_WIDTH,
  parameter bit                 SLAVE_FIFO      = '0,
  parameter bit                 MASTER_FIFO     = '0,
  parameter int                 RESPONSE_DEPTH  = 2
)(
  input   var                           i_clk,
  input   var                           i_rst_n,
  output  var [BUS_CONFIG.id_width-1:0] o_sid,
  input   var [SELECT_WIDTH-1:0]        i_select,
  output  var                           o_response_ack,
  interface.response_slave              slave_if[SLAVES],
  interface.response_master             master_if
);
  pzcorebus_response_if #(BUS_CONFIG) fifo_if[SLAVES]();
  pzcorebus_response_if #(BUS_CONFIG) switch_if();

//--------------------------------------------------------------
//  Slave FIFO
//--------------------------------------------------------------
  for (genvar i = 0;i < SLAVES;++i) begin : g_slave_fifo
    pzcorebus_response_fifo #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .RESPONSE_DEPTH (RESPONSE_DEPTH ),
      .RESPONSE_VALID (SLAVE_FIFO     )
    ) u_slave_fifo (
      .i_clk          (i_clk        ),
      .i_rst_n        (i_rst_n      ),
      .i_clear        ('0           ),
      .o_empty        (),
      .o_almost_full  (),
      .o_full         (),
      .slave_if       (slave_if[i]  ),
      .master_if      (fifo_if[i]   )
    );
  end

//--------------------------------------------------------------
//  Switch
//--------------------------------------------------------------
  logic [SELECT_WIDTH-1:0]  response_select;

  always_comb begin
    o_response_ack  = switch_if.response_last_burst_ack();
  end

  if (EXTERNAL_DECODE) begin : g_response_select
    always_comb begin
      o_sid = switch_if.sid;
    end

    always_comb begin
      response_select = i_select;
    end
  end
  else begin : g_response_select
    always_comb begin
      o_sid = '0;
    end

    always_comb begin
      response_select = switch_if.sid[SELECT_LSB+:SELECT_WIDTH];
    end
  end

  pzcorebus_response_mux #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .SLAVES         (SLAVES         ),
    .SELECTOR_TYPE  (SELECTOR_TYPE  ),
    .SELECT_WIDTH   (SELECT_WIDTH   )
  ) u_mux (
    .i_response_select  (response_select  ),
    .slave_if           (fifo_if          ),
    .master_if          (switch_if        )
  );

//--------------------------------------------------------------
//  Master FIFO
//--------------------------------------------------------------
  pzcorebus_response_fifo #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .RESPONSE_DEPTH (RESPONSE_DEPTH ),
    .RESPONSE_VALID (MASTER_FIFO    )
  ) u_slave_fifo (
    .i_clk          (i_clk      ),
    .i_rst_n        (i_rst_n    ),
    .i_clear        ('0         ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (switch_if  ),
    .master_if      (master_if  )
  );
endmodule
