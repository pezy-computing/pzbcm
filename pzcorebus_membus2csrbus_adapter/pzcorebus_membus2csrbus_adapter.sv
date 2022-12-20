//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_membus2csrbus_adapter
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  MEMBUS_CONFIG       = '0,
  parameter pzcorebus_config  CSRBUS_CONFIG       = '0,
  parameter int               RESPONSE_INFO_DEPTH = 2,
  parameter bit               SLAVE_SLICER        = 0,
  parameter bit               MASTER_SLICER       = 0
)(
  input var                               i_clk,
  input var                               i_rst_n,
  input var [CSRBUS_CONFIG.id_width-1:0]  i_csrbus_id,
  pzcorebus_if.slave                      membus_slave_if,
  pzcorebus_if.master                     csrbus_master_if
);
  initial begin
    assume (CSRBUS_CONFIG.data_width == 32);
    if (MEMBUS_CONFIG.profile == PZCOREBUS_MEMORY_H) begin
      assume (MEMBUS_CONFIG.unit_data_width == 32);
    end
  end

  localparam  int DATA_WIDTH      = MEMBUS_CONFIG.data_width;
  localparam  int UNIT_WIDTH      = 32;
  localparam  int UNIT_BYTE_SIZE  = UNIT_WIDTH / 8;
  localparam  int UNIT_SIZE       = DATA_WIDTH / UNIT_WIDTH;
  localparam  int UNITEN_WIDTH    = get_unit_enable_width(MEMBUS_CONFIG, 1);

  function automatic int get_length_count_width();
    if (MEMBUS_CONFIG.profile == PZCOREBUS_MEMORY_H) begin
      return get_unpacked_length_width(MEMBUS_CONFIG);
    end
    else begin
      return get_burst_length_width(MEMBUS_CONFIG) + $clog2(UNIT_SIZE);
    end
  endfunction

  function automatic int get_data_count_width();
    return $clog2(UNIT_SIZE);
  endfunction

  function automatic int get_uniten_count_width();
    if (MEMBUS_CONFIG.profile == PZCOREBUS_MEMORY_H) begin
      return $clog2(MEMBUS_CONFIG.max_data_width / UNIT_WIDTH);
    end
    else begin
      return $clog2(MEMBUS_CONFIG.data_width / UNIT_WIDTH);
    end
  endfunction

  function automatic int get_word_size();
    if (MEMBUS_CONFIG.profile == PZCOREBUS_MEMORY_H) begin
      return MEMBUS_CONFIG.max_data_width / MEMBUS_CONFIG.data_width;
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_word_count_width();
    int word_size = get_word_size();
    return (word_size <= 1) ? 1 : $clog2(word_size);
  endfunction

  localparam  int UNPACKED_LENGTH_WIDTH = get_unpacked_length_width(MEMBUS_CONFIG);
  localparam  int LENGTH_COUNT_WIDTH    = get_length_count_width();
  localparam  int DATA_COUNT_WIDTH      = get_data_count_width();
  localparam  int UNITEN_COUNT_WIDTH    = get_uniten_count_width();
  localparam  int UNIT_OFFSET_LSB       = $clog2(UNIT_WIDTH / 8);
  localparam  int UNIT_OFFSET_WIDTH     = $clog2(UNIT_SIZE);
  localparam  int WORD_SIZE             = get_word_size();
  localparam  int WORD_COUNT_WIDTH      = get_word_count_width();

  typedef struct packed {
    pzcorebus_response_type             sresp;
    logic [MEMBUS_CONFIG.id_width-1:0]  sid;
    logic [LENGTH_COUNT_WIDTH-1:0]      length;
    logic [UNITEN_COUNT_WIDTH-1:0]      uniten_offset;
  } pzcorebus_response_info;

  pzcorebus_if #(MEMBUS_CONFIG) aligner_if();
  pzcorebus_if #(CSRBUS_CONFIG) csrbus_if();
  logic                         info_fifo_empty;
  logic                         info_fifo_full;
  logic                         info_fifo_push;
  logic                         info_fifo_pop;
  pzcorebus_response_info [1:0] response_info;

//--------------------------------------------------------------
//  Command/Data aligner
//--------------------------------------------------------------
  pzcorebus_command_data_aligner #(
    .BUS_CONFIG     (MEMBUS_CONFIG  ),
    .WAIT_FOR_DATA  (1              ),
    .SLAVE_FIFO     (SLAVE_SLICER   ),
    .COMMAND_DEPTH  (2              ),
    .DATA_DEPTH     (2              ),
    .RESPONSE_DEPTH (2              )
  ) u_aligner (
    .i_clk      (i_clk            ),
    .i_rst_n    (i_rst_n          ),
    .slave_if   (membus_slave_if  ),
    .master_if  (aligner_if       )
  );

//--------------------------------------------------------------
//  Request paht
//--------------------------------------------------------------
  if (1) begin : g_request_path
    logic                                   update;
    logic [1:0]                             write_busy;
    logic                                   read_busy;
    logic                                   busy;
    logic [LENGTH_COUNT_WIDTH-1:0]          aligned_length;
    logic [LENGTH_COUNT_WIDTH-1:0]          length_count;
    logic                                   length_count_last;
    logic [DATA_COUNT_WIDTH-1:0]            data_count;
    logic                                   data_count_last;
    logic [CSRBUS_CONFIG.address_width-1:0] maddr;
    logic                                   write_data_ready;
    logic                                   write_data_active;
    logic                                   write_data_last;

    always_comb begin
      update  =
        csrbus_if.command_ack() ||
        (write_busy && aligner_if.mdata_valid && (!write_data_active));
    end

    always_comb begin
      busy  = (write_busy != '0) || read_busy;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        write_busy  <= '0;
        read_busy   <= '0;
      end
      else if (update && length_count_last) begin
        write_busy  <= '0;
        read_busy   <= '0;
      end
      else if (aligner_if.command_ack()) begin
        write_busy[0] <= aligner_if.mcmd == PZCOREBUS_WRITE;
        write_busy[1] <= aligner_if.mcmd == PZCOREBUS_WRITE_NON_POSTED;
        read_busy     <= aligner_if.mcmd == PZCOREBUS_READ;
      end
    end

    always_comb begin
      aligned_length    = get_aligned_length(aligner_if.maddr, aligner_if.get_unpacked_length());
      length_count_last = length_count == LENGTH_COUNT_WIDTH'(1);
      data_count_last   = data_count == DATA_COUNT_WIDTH'(UNIT_SIZE - 1);
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        length_count  <= LENGTH_COUNT_WIDTH'(0);
        data_count    <= DATA_COUNT_WIDTH'(0);
      end
      else if (aligner_if.command_ack()) begin
        length_count  <= aligned_length;
        data_count    <= aligner_if.maddr[UNIT_OFFSET_LSB+:UNIT_OFFSET_WIDTH];
        maddr         <= aligner_if.maddr[CSRBUS_CONFIG.address_width-1:0];
      end
      else if (update) begin
        length_count  <= length_count - LENGTH_COUNT_WIDTH'(1);
        data_count    <= data_count + DATA_COUNT_WIDTH'(1);
        maddr         <= get_next_maddr(maddr);
      end
    end

    always_comb begin
      write_data_ready  = aligner_if.mdata_valid && (data_count_last || length_count_last);
      write_data_active = aligner_if.mdata_byteen[UNIT_BYTE_SIZE*data_count+:UNIT_BYTE_SIZE] != '0;

      if (!busy) begin
        aligner_if.scmd_accept  = aligner_if.is_posted_command() || (!info_fifo_full);
        aligner_if.sdata_accept = '0;
        csrbus_if.mcmd_valid    = '0;
      end
      else if (read_busy) begin
        aligner_if.scmd_accept  = '0;
        aligner_if.sdata_accept = '0;
        csrbus_if.mcmd_valid    = '1;
      end
      else if (write_data_active) begin
        aligner_if.scmd_accept  = '0;
        aligner_if.sdata_accept = write_data_ready && csrbus_if.scmd_accept;
        csrbus_if.mcmd_valid    = aligner_if.mdata_valid;
      end
      else begin
        aligner_if.scmd_accept  = '0;
        aligner_if.sdata_accept = write_data_ready;
        csrbus_if.mcmd_valid    = '0;
      end

      csrbus_if.mcmd  = get_mcmd(write_busy);
      csrbus_if.mid   = i_csrbus_id;
      csrbus_if.maddr = maddr;
      csrbus_if.mdata = aligner_if.mdata[UNIT_WIDTH*data_count+:UNIT_WIDTH];
    end

    always_comb begin
      csrbus_if.mlength       = '0;
      csrbus_if.minfo         = '0;
      csrbus_if.mdata_valid   = '0;
      csrbus_if.mdata_byteen  = '0;
      csrbus_if.mdata_last    = '0;
    end

    always_comb begin
      info_fifo_push                  = aligner_if.command_non_posted_ack();
      response_info[0].sresp          = get_sresp(aligner_if.mcmd);
      response_info[0].sid            = aligner_if.mid;
      response_info[0].length         = aligned_length;
      response_info[0].uniten_offset  = aligner_if.maddr[UNIT_OFFSET_LSB+:UNITEN_COUNT_WIDTH];
    end
  end

  function automatic logic [LENGTH_COUNT_WIDTH-1:0] get_aligned_length(
    logic [MEMBUS_CONFIG.address_width-1:0] maddr,
    logic [UNPACKED_LENGTH_WIDTH-1:0]       mlength
  );
    logic [LENGTH_COUNT_WIDTH-1:0]  length;
    logic [UNIT_OFFSET_WIDTH-1:0]   offset;

    if (MEMBUS_CONFIG.profile == PZCOREBUS_MEMORY_H) begin
      length  = mlength;
      offset  = UNIT_OFFSET_WIDTH'(0);
    end
    else begin
      length  = {mlength, UNIT_OFFSET_WIDTH'(0)};
      offset  = maddr[UNIT_OFFSET_LSB+:UNIT_OFFSET_WIDTH];
    end

    return length - LENGTH_COUNT_WIDTH'(offset);
  endfunction

  function automatic logic [CSRBUS_CONFIG.address_width-1:0] get_next_maddr(
    logic [CSRBUS_CONFIG.address_width-1:0] maddr
  );
    logic [CSRBUS_CONFIG.address_width-1:0] base;
    logic [CSRBUS_CONFIG.address_width-1:0] delta;
    base  = {maddr[CSRBUS_CONFIG.address_width-1:UNIT_OFFSET_LSB], UNIT_OFFSET_LSB'(0)};
    delta = (CSRBUS_CONFIG.address_width)'(UNIT_WIDTH / 8);
    return base + delta;
  endfunction

  function automatic pzcorebus_command_type get_mcmd(logic [1:0] write_busy);
    if (write_busy[0]) begin
      return PZCOREBUS_WRITE;
    end
    else if (write_busy[1]) begin
      return PZCOREBUS_WRITE_NON_POSTED;
    end
    else begin
      return PZCOREBUS_READ;
    end
  endfunction

  function automatic pzcorebus_response_type get_sresp(
    pzcorebus_command_type  mcmd
  );
    if (mcmd == PZCOREBUS_READ) begin
      return PZCOREBUS_RESPONSE_WITH_DATA;
    end
    else begin
      return PZCOREBUS_RESPONSE;
    end
  endfunction

//--------------------------------------------------------------
//  Response path
//--------------------------------------------------------------
  pzbcm_fifo #(
    .TYPE   (pzcorebus_response_info  ),
    .DEPTH  (RESPONSE_INFO_DEPTH      )
  ) u_response_info_fifo (
    .i_clk          (i_clk            ),
    .i_rst_n        (i_rst_n          ),
    .i_clear        ('0               ),
    .o_empty        (info_fifo_empty  ),
    .o_almost_full  (),
    .o_full         (info_fifo_full   ),
    .o_word_count   (),
    .i_push         (info_fifo_push   ),
    .i_data         (response_info[0] ),
    .i_pop          (info_fifo_pop    ),
    .o_data         (response_info[1] )
  );

  if (1) begin : g_response_path
    logic                           ready;
    logic [LENGTH_COUNT_WIDTH-1:0]  length_count;
    logic [LENGTH_COUNT_WIDTH-1:0]  length_count_next;
    logic [LENGTH_COUNT_WIDTH-1:0]  length_count_last;
    logic [UNITEN_COUNT_WIDTH-1:0]  uniten_count;
    logic [DATA_COUNT_WIDTH-1:0]    data_count;
    logic                           data_count_last;
    logic [2:0]                     sresp_valid;
    logic [DATA_WIDTH-1:0]          sdata;
    logic                           serror;

    always_comb begin
      info_fifo_pop = aligner_if.response_last_ack();
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        ready <= '0;
      end
      else if (aligner_if.response_last_ack()) begin
        ready <= '0;
      end
      else if ((!ready) && (!info_fifo_empty)) begin
        ready <= '1;
      end
    end

    always_comb begin
      length_count_next = length_count + LENGTH_COUNT_WIDTH'(1);
      length_count_last = length_count_next == response_info[1].length;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        length_count  <= LENGTH_COUNT_WIDTH'(0);
      end
      else if ((!ready) && (!info_fifo_empty)) begin
        length_count  <= LENGTH_COUNT_WIDTH'(0);
      end
      else if (csrbus_if.response_ack()) begin
        length_count  <= length_count_next;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        uniten_count  <= UNITEN_COUNT_WIDTH'(0);
      end
      else if ((!ready) && (!info_fifo_empty)) begin
        uniten_count  <= response_info[1].uniten_offset;
      end
      else if (csrbus_if.response_ack()) begin
        uniten_count  <= uniten_count + UNITEN_COUNT_WIDTH'(1);
      end
    end

    always_comb begin
      data_count      = uniten_count[0+:DATA_COUNT_WIDTH];
      data_count_last = data_count == '1;
    end

    always_comb begin
      sresp_valid[0]  = response_info[1].sresp == PZCOREBUS_RESPONSE;
      sresp_valid[1]  = length_count_last;
      sresp_valid[2]  = data_count_last;

      if (!ready) begin
        csrbus_if.mresp_accept  = '0;
        aligner_if.sresp_valid  = '0;
      end
      else if (sresp_valid != '0) begin
        csrbus_if.mresp_accept  = aligner_if.mresp_accept;
        aligner_if.sresp_valid  = csrbus_if.sresp_valid;
      end
      else begin
        csrbus_if.mresp_accept  = '1;
        aligner_if.sresp_valid  = '0;
      end

      aligner_if.sresp        = response_info[1].sresp;
      aligner_if.sid          = response_info[1].sid;
      aligner_if.serror       = csrbus_if.serror || serror;
      aligner_if.sdata        = sdata;
      aligner_if.sinfo        = '0;
      aligner_if.sresp_uniten = get_sresp_uniten(uniten_count);
      aligner_if.sresp_last   = (sresp_valid[1:0] != '0) ? '1 : '0;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        serror  <= '0;
      end
      else if (aligner_if.response_ack()) begin
        serror  <= '0;
      end
      else if (csrbus_if.response_ack()) begin
        serror  <= aligner_if.serror;
      end
    end

    for (genvar i = 0;i < UNIT_SIZE;++i) begin : g_sdata
      if ((i + 1) < UNIT_SIZE) begin : g
        logic [UNIT_WIDTH-1:0]  sdata_latched;
        logic                   match;

        always_comb begin
          match = data_count == DATA_COUNT_WIDTH'(i);
          if (match) begin
            sdata[UNIT_WIDTH*i+:UNIT_WIDTH] = csrbus_if.sdata;
          end
          else begin
            sdata[UNIT_WIDTH*i+:UNIT_WIDTH] = sdata_latched;
          end
        end

        always_ff @(posedge i_clk) begin
          if (csrbus_if.response_ack() && match) begin
            sdata_latched <= sdata[UNIT_WIDTH*i+:UNIT_WIDTH];
          end
        end
      end
      else begin : g
        always_comb begin
          sdata[UNIT_WIDTH*i+:UNIT_WIDTH] = csrbus_if.sdata;
        end
      end
    end
  end

  function automatic logic [UNITEN_WIDTH-1:0] get_sresp_uniten(
    logic [UNITEN_COUNT_WIDTH-1:0]  uniten_count
  );
    logic [WORD_SIZE-1:0][UNIT_SIZE-1:0]  uniten;

    uniten  = '0;
    if (MEMBUS_CONFIG.profile == PZCOREBUS_MEMORY_H) begin
      logic [WORD_COUNT_WIDTH-1:0]  word_count;
      logic [DATA_COUNT_WIDTH-1:0]  data_count;

      if (WORD_SIZE == 1) begin
        word_count  = WORD_COUNT_WIDTH'(0);
      end
      else begin
        word_count  = uniten_count[UNITEN_COUNT_WIDTH-1-:WORD_COUNT_WIDTH];
      end


      data_count  = uniten_count[0+:DATA_COUNT_WIDTH];
      for (int i = 0;i < UNIT_SIZE;++i) begin
        uniten[word_count][i] = data_count >= DATA_COUNT_WIDTH'(i);
      end
    end

    return UNITEN_WIDTH'(uniten);
  endfunction

//--------------------------------------------------------------
//  Slicer
//--------------------------------------------------------------
  pzcorebus_slicer #(
    .BUS_CONFIG     (CSRBUS_CONFIG  ),
    .REQUEST_VALID  (MASTER_SLICER  ),
    .RESPONSE_VALID (MASTER_SLICER  )
  ) u_slicer (
    .i_clk      (i_clk            ),
    .i_rst_n    (i_rst_n          ),
    .slave_if   (csrbus_if        ),
    .master_if  (csrbus_master_if )
  );
endmodule
