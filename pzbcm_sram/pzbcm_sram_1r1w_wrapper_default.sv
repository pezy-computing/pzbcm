//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//
//========================================
module pzbcm_sram_1r1w_wrapper_default
  import  pzbcm_sram_pkg::*;
#(
  parameter pzbcm_sram_params SRAM_PARAMS   = 0,
  parameter type              SRAM_CONFIG   = logic,
  parameter int               DATA_WIDTH    = SRAM_PARAMS.data_width,
  parameter int               POINTER_WIDTH = get_ram_pointer_width(SRAM_PARAMS)
)(
  input   var                     i_write_clk,
  input   var                     i_write_enable,
  input   var [POINTER_WIDTH-1:0] i_write_pointer,
  input   var [DATA_WIDTH-1:0]    i_write_data,
  input   var                     i_read_clk,
  input   var                     i_read_enable,
  input   var [POINTER_WIDTH-1:0] i_read_pointer,
  output  var [DATA_WIDTH-1:0]    o_read_data,
  input   var SRAM_CONFIG         i_sram_config
);
  pzbcm_ram #(
    .WORD_SIZE      (SRAM_PARAMS.words  ),
    .ADDRESS_WIDTH  (POINTER_WIDTH      ),
    .DATA_WIDTH     (DATA_WIDTH         ),
    .BUFFER_OUT     (1                  )
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
