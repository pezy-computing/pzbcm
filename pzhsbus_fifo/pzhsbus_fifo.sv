//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzhsbus_fifo #(
  parameter   type  PAYLOAD       = logic,
  parameter   int   DEPTH         = 8,
  parameter   int   THRESHOLD     = DEPTH,
  parameter   bit   FLAG_FF_OUT   = 1,
  parameter   bit   DATA_FF_OUT   = 1,
  parameter   bit   RESET_RAM     = 0,
  parameter   bit   CLEAR_DATA    = 0,
  parameter   bit   RESET_DATA_FF = 1,
  localparam  type  COUNTER       = logic [$clog2(DEPTH+1)-1:0]
)(
  input   var         i_clk,
  input   var         i_rst_n,
  input   var         i_clear,
  output  var         o_empty,
  output  var         o_almost_full,
  output  var         o_full,
  output  var COUNTER o_word_count,
  pzhsbus_if.slave    slave_if,
  pzhsbus_if.master   master_if
);
  logic empty;
  logic full;

  assign  o_empty         = empty;
  assign  o_full          = full;
  assign  slave_if.ready  = ~full;
  assign  master_if.valid = ~empty;

  pzbcm_fifo #(
    .TYPE           (PAYLOAD        ),
    .DEPTH          (DEPTH          ),
    .THRESHOLD      (THRESHOLD      ),
    .FLAG_FF_OUT    (FLAG_FF_OUT    ),
    .DATA_FF_OUT    (DATA_FF_OUT    ),
    .RESET_RAM      (RESET_RAM      ),
    .CLEAR_DATA     (CLEAR_DATA     ),
    .RESET_DATA_FF  (RESET_DATA_FF  )
  ) u_fifo (
    .i_clk          (i_clk              ),
    .i_rst_n        (i_rst_n            ),
    .i_clear        (i_clear            ),
    .o_empty        (empty              ),
    .o_almost_full  (o_almost_full      ),
    .o_full         (full               ),
    .o_word_count   (o_word_count       ),
    .i_push         (slave_if.valid     ),
    .i_data         (slave_if.payload   ),
    .i_pop          (master_if.ready    ),
    .o_data         (master_if.payload  )
  );
endmodule
