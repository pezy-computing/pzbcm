//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzvbus_fifo #(
  parameter   int   DEPTH       = 8,
  parameter   int   THRESHOLD   = DEPTH,
  parameter   bit   FLAG_FF_OUT = 1,
  parameter   bit   DATA_FF_OUT = 1,
  parameter   bit   RESET_RAM   = 0,
  parameter   bit   CLEAR_DATA  = 0,
  localparam  type  COUNTER     = logic [$clog2(DEPTH+1)-1:0]
)(
  input   var         i_clk,
  input   var         i_rst_n,
  input   var         i_clear,
  output  var         o_empty,
  output  var         o_almost_full,
  output  var         o_full,
  output  var COUNTER o_word_count,
  input   var         i_push,
  pzvbus_if.slave     slave_if,
  input   var         i_pop,
  pzvbus_if.master    master_if
);
  typedef slave_if.__payload_with_valid __payload_with_valid;

  __payload_with_valid  in;
  __payload_with_valid  out;
  logic                 empty;

  assign  o_empty           = empty;
  assign  in.valid          = slave_if.valid;
  assign  in.payload        = slave_if.payload;
  assign  master_if.valid   = (!empty) ? out.valid : '0;
  assign  master_if.payload = out.payload;

  pzbcm_fifo #(
    .TYPE         (__payload_with_valid ),
    .DEPTH        (DEPTH                ),
    .THRESHOLD    (THRESHOLD            ),
    .FLAG_FF_OUT  (FLAG_FF_OUT          ),
    .DATA_FF_OUT  (DATA_FF_OUT          ),
    .RESET_RAM    (RESET_RAM            ),
    .CLEAR_DATA   (CLEAR_DATA           )
  ) u_fifo (
    .i_clk          (i_clk          ),
    .i_rst_n        (i_rst_n        ),
    .i_clear        (i_clear        ),
    .o_empty        (empty          ),
    .o_almost_full  (o_almost_full  ),
    .o_full         (o_full         ),
    .o_word_count   (o_word_count   ),
    .i_push         (i_push         ),
    .i_data         (in             ),
    .i_pop          (i_pop          ),
    .o_data         (out            )
  );
endmodule
