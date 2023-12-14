//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_sram_fifo
  import  pzbcm_sram_pkg::*;
#(
  parameter pzbcm_sram_params SRAM_PARAMS = '0,
  parameter int               WIDTH       = SRAM_PARAMS.data_width,
  parameter type              TYPE        = logic [WIDTH-1:0],
  parameter int               DEPTH       = SRAM_PARAMS.words,
  parameter int               THRESHOLD   = DEPTH,
  parameter type              SRAM_CONFIG = logic
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_clear,
  input   var SRAM_CONFIG i_sram_config,
  output  var             o_empty,
  output  var             o_completely_empty,
  output  var             o_almost_full,
  output  var             o_full,
  output  var             o_completely_full,
  input   var             i_push,
  input   var TYPE        i_data,
  input   var             i_pop,
  output  var TYPE        o_data
);
  localparam  int POINTER_WIDTH = $clog2(DEPTH);

  logic                         empty;
  logic                         almost_full;
  logic                         full;
  logic                         write_ack;
  logic                         read_ack;
  logic [POINTER_WIDTH-1:0]     wp;
  logic [POINTER_WIDTH-1:0]     rp;
  pzbcm_sram_if #(SRAM_PARAMS)  sram_if();

  always_comb begin
    o_empty             = sram_if.fifo_empty;
    o_completely_empty  = sram_if.fifo_empty && empty && (!sram_if.read_busy);
    o_almost_full       = almost_full;
    o_full              = full;
    o_completely_full   = full && sram_if.fifo_full;
  end

//--------------------------------------------------------------
//  FIFO controller
//--------------------------------------------------------------
  always_comb begin
    write_ack = sram_if.write_ack();
    read_ack  = sram_if.read_ack();
  end

  pzbcm_fifo_controller #(
    .TYPE               (TYPE           ),
    .DEPTH              (DEPTH          ),
    .THRESHOLD          (THRESHOLD      ),
    .FLAG_FF_OUT        (1              ),
    .DATA_FF_OUT        (0              ),
    .PUSH_ON_CLEAR      (0              ),
    .RAM_WORDS          (DEPTH          ),
    .RAM_POINTER_WIDTH  (POINTER_WIDTH  ),
    .MATCH_COUNT_WIDTH  (0              )
  ) u_controller (
    .i_clk            (i_clk        ),
    .i_rst_n          (i_rst_n      ),
    .i_clear          (i_clear      ),
    .o_empty          (empty        ),
    .o_almost_full    (almost_full  ),
    .o_full           (full         ),
    .i_push           (write_ack    ),
    .i_data           ('0           ),
    .i_pop            (read_ack     ),
    .o_word_count     (),
    .o_write_pointer  (wp           ),
    .o_write_to_ff    (),
    .o_write_to_ram   (),
    .o_read_pointer   (rp           ),
    .o_read_from_ram  ()
  );

//--------------------------------------------------------------
//  SRAM
//--------------------------------------------------------------
  always_comb begin
    sram_if.write_valid   = i_push && (!full);
    sram_if.write_pointer = wp;
    sram_if.write_data    = i_data;
  end

  always_comb begin
    sram_if.read_valid    = !empty;
    sram_if.read_pointer  = rp;
    sram_if.read_info     = '0;
  end

  always_comb begin
    sram_if.read_data_ready = i_pop;
    o_data                  = TYPE'(sram_if.read_data.data);
  end

  pzbcm_sram #(
    .PARAMS           (SRAM_PARAMS  ),
    .READ_INFO_ENABLE (0            ),
    .OUTPUT_FIFO      (1            ),
    .SRAM_CONFIG      (SRAM_CONFIG  )
  ) u_sram (
    .i_write_clk    (i_clk          ),
    .i_read_clk     (i_clk          ),
    .i_read_rst_n   (i_rst_n        ),
    .i_clear        (i_clear        ),
    .i_sram_config  (i_sram_config  ),
    .port_if        (sram_if        )
  );
endmodule
