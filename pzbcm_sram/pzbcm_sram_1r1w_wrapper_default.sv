//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_sram_1r1w_wrapper_default #(
  parameter int WORDS         = 2,
  parameter int DATA_WIDTH    = 8,
  parameter int POINTER_WIDTH = 2,
  parameter bit SINGLE_CLOCK  = 1
)(
  input   var                     i_write_clk,
  input   var                     i_write_enable,
  input   var [POINTER_WIDTH-1:0] i_write_pointer,
  input   var [DATA_WIDTH-1:0]    i_write_data,
  input   var                     i_read_clk,
  input   var                     i_read_enable,
  input   var [POINTER_WIDTH-1:0] i_read_pointer,
  output  var [DATA_WIDTH-1:0]    o_read_data
);
  pzbcm_ram #(
    .WORD_SIZE      (WORDS            ),
    .ADDRESS_WIDTH  (POINTER_WIDTH    ),
    .DATA_WIDTH     (DATA_WIDTH       ),
    .BUFFER_OUT     (1                )
  ) u_ram (
    .i_clk    (i_write_clk      ),
    .i_rst_n  ('0               ),
    .i_clr    ('0               ),
    .i_mea    (i_write_enable   ),
    .i_wea    ('1               ),
    .i_adra   (i_write_pointer  ),
    .i_da     (i_write_data     ),
    .i_meb    (i_read_enable    ),
    .i_adrb   (i_read_pointer   ),
    .o_qb     (o_read_data      )
  );
endmodule
