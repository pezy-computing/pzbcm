//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_fifo #(
  parameter   int   WIDTH             = 8,
  parameter   type  TYPE              = logic [WIDTH-1:0],
  parameter   int   DEPTH             = 8,
  parameter   int   THRESHOLD         = DEPTH,
  parameter   bit   FLAG_FF_OUT       = 1,
  parameter   bit   DATA_FF_OUT       = 1,
  parameter   bit   RESET_RAM         = 0,
  parameter   bit   RESET_DATA_FF     = 1,
  parameter   bit   CLEAR_DATA        = 0,
  parameter   bit   PUSH_ON_CLEAR     = 0,
  parameter   bit   ENABLE_GRAY       = 0,
  parameter   int   MATCH_COUNT_WIDTH = 0,
  localparam  type  COUNTER           = logic [$clog2(DEPTH+1)-1:0]
)(
  input   var         i_clk,
  input   var         i_rst_n,
  input   var         i_clear,
  output  var         o_empty,
  output  var         o_almost_full,
  output  var         o_full,
  output  var COUNTER o_word_count,
  input   var         i_push,
  input   var TYPE    i_data,
  input   var         i_pop,
  output  var TYPE    o_data
);
  localparam  int RAM_WORDS = (DATA_FF_OUT) ? DEPTH - 1 : DEPTH;

  initial begin
    assume (!(CLEAR_DATA && PUSH_ON_CLEAR));
  end

  logic clear_data;

  always_comb begin
    clear_data  = CLEAR_DATA && i_clear;
  end

//--------------------------------------------------------------
//  controller
//--------------------------------------------------------------
  localparam  int POINTER_WIDTH = (RAM_WORDS >= 2) ? $clog2(RAM_WORDS) : 1;

  logic [POINTER_WIDTH-1:0] write_pointer;
  logic                     write_to_ff;
  logic                     write_to_ram;
  logic [POINTER_WIDTH-1:0] read_pointer;
  logic                     read_from_ram;

  pzbcm_fifo_controller #(
    .TYPE               (TYPE               ),
    .DEPTH              (DEPTH              ),
    .THRESHOLD          (THRESHOLD          ),
    .FLAG_FF_OUT        (FLAG_FF_OUT        ),
    .DATA_FF_OUT        (DATA_FF_OUT        ),
    .PUSH_ON_CLEAR      (PUSH_ON_CLEAR      ),
    .RAM_WORDS          (RAM_WORDS          ),
    .RAM_POINTER_WIDTH  (POINTER_WIDTH      ),
    .ENABLE_GRAY        (ENABLE_GRAY        ),
    .MATCH_COUNT_WIDTH  (MATCH_COUNT_WIDTH  )
  ) u_controller (
    .i_clk            (i_clk          ),
    .i_rst_n          (i_rst_n        ),
    .i_clear          (i_clear        ),
    .o_empty          (o_empty        ),
    .o_almost_full    (o_almost_full  ),
    .o_full           (o_full         ),
    .i_push           (i_push         ),
    .i_data           (i_data         ),
    .i_pop            (i_pop          ),
    .o_word_count     (o_word_count   ),
    .o_write_pointer  (write_pointer  ),
    .o_write_to_ff    (write_to_ff    ),
    .o_write_to_ram   (write_to_ram   ),
    .o_read_pointer   (read_pointer   ),
    .o_read_from_ram  (read_from_ram  )
  );

//--------------------------------------------------------------
//  RAM
//--------------------------------------------------------------
  TYPE  ram_read_data;

  if (RAM_WORDS >= 1) begin : g_ram
    pzbcm_ram #(
      .WORD_SIZE      (RAM_WORDS      ),
      .ADDRESS_WIDTH  (POINTER_WIDTH  ),
      .DATA_TYPE      (TYPE           ),
      .BUFFER_OUT     (0              ),
      .USE_RESET      (RESET_RAM      )
    ) u_ram (
      .i_clk    (i_clk          ),
      .i_rst_n  (i_rst_n        ),
      .i_clr    (clear_data     ),
      .i_mea    ('1             ),
      .i_wea    (write_to_ram   ),
      .i_adra   (write_pointer  ),
      .i_da     (i_data         ),
      .i_meb    ('1             ),
      .i_adrb   (read_pointer   ),
      .o_qb     (ram_read_data  )
    );
  end
  else begin : g_no_ram
    always_comb begin
      ram_read_data = TYPE'(0);
    end
  end

//--------------------------------------------------------------
//  output control
//--------------------------------------------------------------
  if (DATA_FF_OUT) begin : g_data_out
    TYPE  data_out;

    always_comb begin
      o_data  = data_out;
    end

    if (RESET_DATA_FF) begin : g
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          data_out  <= TYPE'(0);
        end
        else if (clear_data) begin
          data_out  <= TYPE'(0);
        end
        else if (write_to_ff) begin
          data_out  <= i_data;
        end
        else if (read_from_ram) begin
          data_out  <= ram_read_data;
        end
      end
    end
    else begin : g
      always_ff @(posedge i_clk) begin
        if (clear_data) begin
          data_out  <= TYPE'(0);
        end
        else if (write_to_ff) begin
          data_out  <= i_data;
        end
        else if (read_from_ram) begin
          data_out  <= ram_read_data;
        end
      end
    end
  end
  else begin : g_data_out
    always_comb begin
      o_data  = ram_read_data;
    end
  end
endmodule
