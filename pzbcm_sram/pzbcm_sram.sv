//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_sram
  import  pzbcm_sram_pkg::*;
#(
  parameter pzbcm_sram_params SRAM_PARAMS       = '0,
  parameter int               BANKS             = 1,
  parameter bit               BANK_LSB          = 0,
  parameter bit               READ_INFO_ENABLE  = 0,
  parameter type              READ_INFO         = logic,
  parameter bit               OUTPUT_FIFO       = 1,
  parameter bit               WRITE_FIRST       = 1,
  parameter type              SRAM_CONFIG       = logic
)(
  input var             i_write_clk,
  input var             i_read_clk,
  input var             i_read_rst_n,
  input var             i_clear,
  input var SRAM_CONFIG i_sram_config,
  pzbcm_sram_if.sram    port_if
);
  localparam  int DATA_WIDTH        = SRAM_PARAMS.data_width;
  localparam  int POINTER_WIDTH     = get_pointer_width(SRAM_PARAMS, BANKS);
  localparam  int BANK_WIDTH        = get_bank_width(BANKS);
  localparam  int RAM_POINTER_WIDTH = get_ram_pointer_width(SRAM_PARAMS);
  localparam  int RAM_POINTER_LSB   = get_ram_pointer_lsb(BANKS, BANK_LSB);
  localparam  int INFO_WIDTH        = (READ_INFO_ENABLE) ? $bits(READ_INFO) : 0;

  logic [BANKS-1:0]                 write_ready;
  logic [BANKS-1:0]                 write_enable;
  logic [BANKS-1:0]                 read_ready;
  logic [BANKS-1:0]                 read_enable;
  logic [BANKS-1:0][DATA_WIDTH-1:0] read_data;
  logic [BANKS-1:0]                 read_data_valid;
  READ_INFO                         read_info;
  logic                             read_busy;
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
      if (!SRAM_PARAMS.single_port_ram) begin
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

    if (SRAM_PARAMS.single_port_ram) begin : g
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

      if (SRAM_PARAMS.id >= 0) begin : g
        `PZBCM_SRAM_1RW_WRAPPER #(
          .SRAM_PARAMS  (SRAM_PARAMS  ),
          .SRAM_CONFIG  (SRAM_CONFIG  )
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
        pzbcm_sram_1rw_wrapper_default #(
          .SRAM_PARAMS  (SRAM_PARAMS  ),
          .SRAM_CONFIG  (SRAM_CONFIG  )
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
    end
    else begin : g
      if (SRAM_PARAMS.id >= 0) begin : g
        `PZBCM_SRAM_1R1W_WRAPPER #(
          .SRAM_PARAMS  (SRAM_PARAMS  ),
          .SRAM_CONFIG  (SRAM_CONFIG  )
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
      else begin : g
        pzbcm_sram_1r1w_wrapper_default #(
          .SRAM_PARAMS  (SRAM_PARAMS  ),
          .SRAM_CONFIG  (SRAM_CONFIG  )
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
  end

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

//--------------------------------------------------------------
//  Read Data
//--------------------------------------------------------------
  if (1) begin : g_read_data_valid
    logic [SRAM_PARAMS.read_latency-1:0][BANKS-1:0] delay;

    always_ff @(posedge i_read_clk, negedge i_read_rst_n) begin
      if (!i_read_rst_n) begin
        delay <= '0;
      end
      else if (i_clear) begin
        delay <= '0;
      end
      else begin
        for (int i = 0;i < SRAM_PARAMS.read_latency;++i) begin
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
      port_if.read_busy = read_busy;
    end

    always_comb begin
      read_busy       = delay != '0;
      read_data_valid = delay[SRAM_PARAMS.read_latency-1];
    end
  end

  if (READ_INFO_ENABLE) begin : g_read_info
    pzbcm_delay #(
      .DELAY  (SRAM_PARAMS.read_latency ),
      .TYPE   (READ_INFO                )
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
    localparam  int FIFO_DATA_WIDTH = SRAM_PARAMS.data_width + INFO_WIDTH;
    localparam  int FIFO_DEPTH      = 2 + SRAM_PARAMS.read_latency;

    logic                       empty;
    logic                       almost_full;
    logic                       full;
    logic                       push;
    logic [FIFO_DATA_WIDTH-1:0] push_data;
    logic                       pop;
    logic [FIFO_DATA_WIDTH-1:0] pop_data;

    always_comb begin
      port_if.fifo_empty        = empty;
      port_if.fifo_almost_full  = almost_full;
      port_if.fifo_full         = full;
    end

    always_comb begin
      fifo_ready  = (!almost_full) || ((!read_busy) && (!full));
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
      .o_almost_full  (almost_full  ),
      .o_full         (full         ),
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
      fifo_ready                = '1;
      port_if.fifo_empty        = '1;
      port_if.fifo_almost_full  = '0;
      port_if.fifo_full         = '0;
    end

    always_comb begin
      port_if.read_data_valid = read_data_valid != '0;
      port_if.read_data.data  = ram_read_data;
      port_if.read_data.info  = read_info;
    end
  end
endmodule
