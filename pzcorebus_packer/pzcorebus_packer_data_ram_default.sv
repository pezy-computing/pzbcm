//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_packer_data_ram_default #(
  parameter int WORD_SIZE     = 0,
  parameter int ADDRESS_WIDTH = 0,
  parameter int DATA_WIDTH    = 0
)(
  input   var                     i_clk,
  input   var                     i_write_valid,
  input   var [ADDRESS_WIDTH-1:0] i_write_address,
  input   var [DATA_WIDTH-1:0]    i_write_data,
  input   var                     i_read_valid,
  input   var [ADDRESS_WIDTH-1:0] i_read_address,
  output  var [DATA_WIDTH-1:0]    o_read_data
);
  pzbcm_ram #(
    .WORD_SIZE      (WORD_SIZE      ),
    .ADDRESS_WIDTH  (ADDRESS_WIDTH  ),
    .DATA_WIDTH     (DATA_WIDTH     ),
    .BUFFER_OUT     (1              )
  ) u_ram (
    .i_clk    (i_clk            ),
    .i_rst_n  ('1               ),
    .i_clr    ('0               ),
    .i_mea    (i_write_valid    ),
    .i_wea    (i_write_valid    ),
    .i_adra   (i_write_address  ),
    .i_da     (i_write_data     ),
    .i_meb    (i_read_valid     ),
    .i_adrb   (i_read_address   ),
    .o_qb     (o_read_data      )
  );
endmodule
