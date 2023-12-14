//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_sram_1rw_wrapper_default #(
  parameter int WORDS         = 2,
  parameter int DATA_WIDTH    = 8,
  parameter int POINTER_WIDTH = 2
)(
  input   var                     i_clk,
  input   var                     i_enable,
  input   var                     i_write,
  input   var [POINTER_WIDTH-1:0] i_pointer,
  input   var [DATA_WIDTH-1:0]    i_write_data,
  output  var [DATA_WIDTH-1:0]    o_read_data
);
  logic mea;
  logic meb;

  always_comb begin
    mea = i_enable && (i_write == '1);
    meb = i_enable && (i_write == '0);
  end

  pzbcm_ram #(
    .WORD_SIZE      (WORDS            ),
    .ADDRESS_WIDTH  (POINTER_WIDTH    ),
    .DATA_WIDTH     (DATA_WIDTH       ),
    .BUFFER_OUT     (1                )
  ) u_sram (
    .i_clk    (i_clk        ),
    .i_rst_n  ('0           ),
    .i_clr    ('0           ),
    .i_mea    (mea          ),
    .i_wea    ('1           ),
    .i_adra   (i_pointer    ),
    .i_da     (i_write_data ),
    .i_meb    (meb          ),
    .i_adrb   (i_pointer    ),
    .o_qb     (o_read_data  )
  );
endmodule
