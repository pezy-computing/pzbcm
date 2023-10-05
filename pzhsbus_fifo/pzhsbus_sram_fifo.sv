//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzhsbus_sram_fifo #(
  parameter type  PAYLOAD       = logic,
  parameter int   DEPTH         = 8,
  parameter int   THRESHOLD     = DEPTH,
  parameter type  SRAM_CONFIG   = logic,
  parameter int   READ_LATENCY  = 1,
  parameter int   SRAM_ID       = 0
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_clear,
  output  var             o_empty,
  output  var             o_completely_empty,
  output  var             o_almost_full,
  output  var             o_full,
  output  var             o_completely_full,
  input   var SRAM_CONFIG i_sram_config,
  pzhsbus_if.slave        slave_if,
  pzhsbus_if.master       master_if
);
  logic [1:0] empty;
  logic       almost_full;
  logic [1:0] full;
  logic       push;
  PAYLOAD     push_payload;
  logic       pop;
  PAYLOAD     pop_payload;

  always_comb begin
    o_empty             = empty[0];
    o_completely_empty  = empty[1];
    o_almost_full       = almost_full;
    o_full              = full[0];
    o_completely_full   = full[1];
  end

  always_comb begin
    slave_if.ready  = !full[0];
    push            = slave_if.valid;
    push_payload    = slave_if.payload;
  end

  always_comb begin
    pop               = master_if.ready;
    master_if.valid   = !empty[0];
    master_if.payload = pop_payload;
  end

  pzbcm_sram_fifo #(
    .TYPE         (PAYLOAD      ),
    .DEPTH        (DEPTH        ),
    .THRESHOLD    (THRESHOLD    ),
    .SRAM_CONFIG  (SRAM_CONFIG  ),
    .READ_LATENCY (READ_LATENCY ),
    .SRAM_ID      (SRAM_ID      )
  ) u_fifo (
    .i_clk              (i_clk          ),
    .i_rst_n            (i_rst_n        ),
    .i_clear            (i_clear        ),
    .i_sram_config      (i_sram_config  ),
    .o_empty            (empty[0]       ),
    .o_completely_empty (empty[1]       ),
    .o_almost_full      (almost_full    ),
    .o_full             (full[0]        ),
    .o_completely_full  (full[1]        ),
    .i_push             (push           ),
    .i_data             (push_payload   ),
    .i_pop              (pop            ),
    .o_data             (pop_payload    )
  );
endmodule
