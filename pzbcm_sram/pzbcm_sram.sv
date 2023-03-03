//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_sram #(
  parameter int   WORDS             = 2,
  parameter int   DATA_WIDTH        = 8,
  parameter int   BANKS             = 1,
  parameter bit   BANK_LSB          = 1,
  parameter bit   SINGLE_PORT_RAM   = 1,
  parameter bit   SINGLE_CLOCK      = 1,
  parameter bit   READ_INFO_ENABLE  = 0,
  parameter type  READ_INFO         = logic,
  parameter bit   OUTPUT_FIFO       = 1,
  parameter type  SRAM_CONFIG       = logic,
  parameter bit   WRITE_FIRST       = 1,
  parameter int   READ_LATENCY      = 1,
  parameter int   SRAM_ID           = 0
)(
  input var             i_write_clk,
  input var             i_read_clk,
  input var             i_read_rst_n,
  input var             i_clear,
  input var SRAM_CONFIG i_sram_config,
  pzbcm_sram_if         port_if
);
  function automatic int calc_pointer_width(int width);
    if (width > 1) begin
      return $clog2(width);
    end
    else begin
      return 1;
    end
  endfunction

  localparam  int POINTER_WIDTH     = calc_pointer_width(WORDS);
  localparam  int BANK_WIDTH        = calc_pointer_width(BANKS);
  localparam  int RAM_WORDS         = WORDS / BANKS;
  localparam  int RAM_POINTER_WIDTH = calc_pointer_width(RAM_WORDS);
  localparam  int RAM_POINTER_LSB   = (BANK_LSB && (BANKS > 1)) ? BANK_WIDTH : 0;
  localparam  int INFO_WIDTH        = (READ_INFO_ENABLE) ? $bits(READ_INFO) : 0;

  function automatic logic match_bank(
    int                       bank_index,
    logic [POINTER_WIDTH-1:0] pointer
  );
    if (BANKS == 1) begin
      return '1;
    end
    else if (BANK_LSB) begin
      return pointer[0+:BANK_WIDTH] == BANK_WIDTH'(bank_index);
    end
    else begin
      return pointer[POINTER_WIDTH-1-:BANK_WIDTH] == BANK_WIDTH'(bank_index);
    end
  endfunction

  logic [BANKS-1:0]                 write_ready;
  logic [BANKS-1:0]                 write_enable;
  logic [BANKS-1:0]                 read_ready;
  logic [BANKS-1:0]                 read_enable;
  logic [BANKS-1:0][DATA_WIDTH-1:0] read_data;
  logic [BANKS-1:0]                 read_data_valid;
  READ_INFO                         read_info;
  logic [DATA_WIDTH-1:0]            ram_read_data;
  logic                             fifo_ready;

//--------------------------------------------------------------
//  SRAM instance
//--------------------------------------------------------------
  `ifndef PZBCM_SRAM_1RW_WRAPPER
    `define PZBCM_SRAM_1RW_WRAPPER  pzbcm_sram_1rw_wrapper_default
  `endif

  `ifndef PZBCM_SRAM_1R1W_WRAPPER
    `define PZBCM_SRAM_1R1W_WRAPPER pzbcm_sram_1r1w_wrapper_default
  `endif

  always_comb begin
    port_if.write_ready = write_ready != '0;
    port_if.read_ready  = read_ready  != '0;
  end

  for (genvar i = 0;i < BANKS;++i) begin : g_bank
    logic                         write_bank;
    logic [RAM_POINTER_WIDTH-1:0] write_pointer;
    logic                         read_bank;
    logic [RAM_POINTER_WIDTH-1:0] read_pointer;

    always_comb begin
      write_bank    = match_bank(i, port_if.write_pointer);
      write_pointer = port_if.write_pointer[RAM_POINTER_LSB+:RAM_POINTER_WIDTH];
      read_bank     = match_bank(i, port_if.read_pointer);
      read_pointer  = port_if.read_pointer[RAM_POINTER_LSB+:RAM_POINTER_WIDTH];
      if (!SINGLE_PORT_RAM) begin
        write_ready[i]  = write_bank;
        write_enable[i] = port_if.write_valid && write_ready[i];
        read_ready[i]   = read_bank && fifo_ready;
        read_enable[i]  = port_if.read_valid && read_ready[i];
      end
      else if (WRITE_FIRST) begin
        write_ready[i]  = write_bank;
        write_enable[i] = port_if.write_valid && write_ready[i];
        read_ready[i]   = read_bank && fifo_ready && (!write_enable[i]);
        read_enable[i]  = port_if.read_valid && read_ready[i];
      end
      else begin
        read_ready[i]   = read_bank && fifo_ready;
        read_enable[i]  = port_if.read_valid && read_ready[i];
        write_ready[i]  = write_bank && (!read_enable[i]);
        write_enable[i] = port_if.write_valid && write_ready[i];
      end
    end

    if (SINGLE_PORT_RAM) begin : g
      logic                         enable;
      logic [RAM_POINTER_WIDTH-1:0] ram_pointer;

      always_comb begin
        enable  = write_enable[i] || read_enable[i];
        if (write_enable[i]) begin
          ram_pointer = write_pointer;
        end
        else begin
          ram_pointer = read_pointer;
        end
      end

      `PZBCM_SRAM_1RW_WRAPPER #(
        .WORDS          (RAM_WORDS          ),
        .DATA_WIDTH     (DATA_WIDTH         ),
        .POINTER_WIDTH  (RAM_POINTER_WIDTH  ),
        .SRAM_CONFIG    (SRAM_CONFIG        ),
        .SRAM_ID        (SRAM_ID            )
      ) u_sram (
        .i_clk          (i_write_clk        ),
        .i_enable       (enable             ),
        .i_write        (write_enable[i]    ),
        .i_pointer      (ram_pointer        ),
        .i_write_data   (port_if.write_data ),
        .o_read_data    (read_data[i]       ),
        .i_sram_config  (i_sram_config      )
      );
    end
    else begin : g
      `PZBCM_SRAM_1R1W_WRAPPER #(
        .WORDS          (RAM_WORDS          ),
        .DATA_WIDTH     (DATA_WIDTH         ),
        .POINTER_WIDTH  (RAM_POINTER_WIDTH  ),
        .SINGLE_CLOCK   (SINGLE_CLOCK       ),
        .SRAM_CONFIG    (SRAM_CONFIG        ),
        .SRAM_ID        (SRAM_ID            )
      ) u_sram (
        .i_write_clk      (i_write_clk        ),
        .i_write_enable   (write_enable[i]    ),
        .i_write_pointer  (write_pointer      ),
        .i_write_data     (port_if.write_data ),
        .i_read_clk       (i_read_clk         ),
        .i_read_enable    (read_enable[i]     ),
        .i_read_pointer   (read_pointer       ),
        .o_read_data      (read_data[i]       ),
        .i_sram_config    (i_sram_config      )
      );
    end
  end

//--------------------------------------------------------------
//  Read Data
//--------------------------------------------------------------
  if (1) begin : g_read_data_valid
    logic [READ_LATENCY-1:0][BANKS-1:0] delay;

    always_ff @(posedge i_read_clk, negedge i_read_rst_n) begin
      if (!i_read_rst_n) begin
        delay <= '0;
      end
      else if (i_clear) begin
        delay <= '0;
      end
      else begin
        for (int i = 0;i < READ_LATENCY;++i) begin
          if (i == 0) begin
            delay[i]  <= read_enable;
          end
          else begin
            delay[i]  <= delay[i-1];
          end
        end
      end
    end

    always_comb begin
      read_data_valid = delay[READ_LATENCY-1];
    end
  end

  if (READ_INFO_ENABLE) begin : g_read_info
    pzbcm_delay #(
      .DELAY  (READ_LATENCY ),
      .TYPE   (READ_INFO    )
    ) u_read_info_delay (
      .i_clk    (i_read_clk         ),
      .i_rst_n  (i_read_rst_n       ),
      .i_d      (port_if.read_info  ),
      .o_d      (read_info          )
    );
  end
  else begin : g_read_info
    always_comb begin
      read_info = READ_INFO'(0);
    end
  end

  pzbcm_selector #(
    .WIDTH    (DATA_WIDTH ),
    .ENTRIES  (BANKS      )
  ) u_read_data_mux ();

  always_comb begin
    ram_read_data = u_read_data_mux.onehot_mux(read_data_valid, read_data);
  end

  if (OUTPUT_FIFO) begin : g_output_data
    localparam  int FIFO_DATA_WIDTH = DATA_WIDTH + INFO_WIDTH;
    localparam  int FIFO_DEPTH      = 2 + READ_LATENCY;

    logic                       empty;
    logic                       full;
    logic                       push;
    logic [FIFO_DATA_WIDTH-1:0] push_data;
    logic                       pop;
    logic [FIFO_DATA_WIDTH-1:0] pop_data;

    always_comb begin
      fifo_ready  = !full;
    end

    always_comb begin
      push      = read_data_valid != '0;
      push_data = FIFO_DATA_WIDTH'({read_info, ram_read_data});
    end

    pzbcm_fifo #(
      .WIDTH      (FIFO_DATA_WIDTH  ),
      .DEPTH      (FIFO_DEPTH       ),
      .THRESHOLD  (2                )
    ) u_read_data_fifo (
      .i_clk          (i_read_clk   ),
      .i_rst_n        (i_read_rst_n ),
      .i_clear        (i_clear      ),
      .o_empty        (empty        ),
      .o_almost_full  (full         ),
      .o_full         (),
      .o_word_count   (),
      .i_push         (push         ),
      .i_data         (push_data    ),
      .i_pop          (pop          ),
      .o_data         (pop_data     )
    );

    always_comb begin
      pop                     = port_if.read_data_ready;
      port_if.read_data_valid = !empty;
      port_if.read_data.data  = pop_data[0+:DATA_WIDTH];
      if (READ_INFO_ENABLE) begin
        port_if.read_data.info  = READ_INFO'(pop_data[FIFO_DATA_WIDTH-1-:$bits(READ_INFO)]);
      end
      else begin
        port_if.read_data.info  = READ_INFO'(0);
      end
    end
  end
  else begin : g_output_data
    always_comb begin
      fifo_ready  = '1;
    end

    always_comb begin
      port_if.read_data_valid = read_data_valid != '0;
      port_if.read_data.data  = ram_read_data;
      port_if.read_data.info  = read_info;
    end
  end
endmodule
