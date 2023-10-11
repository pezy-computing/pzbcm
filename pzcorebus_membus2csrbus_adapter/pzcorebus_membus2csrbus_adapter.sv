//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_membus2csrbus_adapter
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  MEMBUS_CONFIG           = '0,
  parameter pzcorebus_config  CSRBUS_CONFIG           = '0,
  parameter int               MAX_NON_POSTED_REQUESTS = 2,
  parameter int               RESPONSE_INFO_DEPTH     = MAX_NON_POSTED_REQUESTS,
  parameter bit [1:0]         SLAVE_SLICER            = '1,
  parameter bit [1:0]         MASTER_SLICER           = '1,
  parameter int               VALID_ADDRESS_WIDTH     = CSRBUS_CONFIG.address_width
)(
  input var                               i_clk,
  input var                               i_rst_n,
  input var [CSRBUS_CONFIG.id_width-1:0]  i_base_id,
  input var                               i_force_np_write,
  input var                               i_wait_for_all_responses,
  pzcorebus_if.slave                      membus_slave_if,
  pzcorebus_if.master                     csrbus_master_if
);
  `include  "pzcorebus_macros.svh"

  initial begin
    assume (CSRBUS_CONFIG.data_width == 32);
    assume (VALID_ADDRESS_WIDTH inside {[1:CSRBUS_CONFIG.address_width]});
    if (is_memory_h_profile(MEMBUS_CONFIG)) begin
      assume (MEMBUS_CONFIG.unit_data_width == 32);
    end
  end

  typedef logic [get_request_info_width(MEMBUS_CONFIG, 1)-1:0]  pzcorebus_request_info;

  typedef struct packed {
    pzcorebus_request_info  minfo;
    logic                   force_np_write;
    logic                   wait_for_all_responses;
  } pzcorebus_sideband_info;

  localparam  int ADDRESS_WIDTH   = CSRBUS_CONFIG.address_width;
  localparam  int DATA_WIDTH      = MEMBUS_CONFIG.data_width;
  localparam  int UNIT_WIDTH      = 32;
  localparam  int UNIT_BYTE_SIZE  = UNIT_WIDTH / 8;
  localparam  int UNIT_SIZE       = DATA_WIDTH / UNIT_WIDTH;
  localparam  int UNITEN_WIDTH    = get_unit_enable_width(MEMBUS_CONFIG, 1);

  function automatic int get_minfo_width();
    if (MEMBUS_CONFIG.request_info_width >= 1) begin
      return $bits(pzcorebus_sideband_info);
    end
    else begin
      return $bits(pzcorebus_sideband_info) - $bits(pzcorebus_request_info);
    end
  endfunction

  function automatic int get_data_count_width();
    return $clog2(UNIT_SIZE);
  endfunction

  function automatic int get_uniten_count_width();
    if (is_memory_h_profile(MEMBUS_CONFIG)) begin
      return $clog2(MEMBUS_CONFIG.max_data_width / UNIT_WIDTH);
    end
    else begin
      return $clog2(MEMBUS_CONFIG.data_width / UNIT_WIDTH);
    end
  endfunction

  function automatic int get_word_size();
    if (is_memory_h_profile(MEMBUS_CONFIG)) begin
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

  localparam  int MINFO_WIDTH           = get_minfo_width();
  localparam  int UNPACKED_LENGTH_WIDTH = get_unpacked_length_width(MEMBUS_CONFIG);
  localparam  int LENGTH_COUNT_WIDTH    = UNPACKED_LENGTH_WIDTH;
  localparam  int DATA_COUNT_WIDTH      = get_data_count_width();
  localparam  int UNITEN_COUNT_WIDTH    = get_uniten_count_width();
  localparam  int UNIT_OFFSET_LSB       = $clog2(UNIT_WIDTH / 8);
  localparam  int UNIT_OFFSET_WIDTH     = $clog2(UNIT_SIZE);
  localparam  int WORD_SIZE             = get_word_size();
  localparam  int WORD_COUNT_WIDTH      = get_word_count_width();
  localparam  int UNIT_ADDRESS_WIDTH    = VALID_ADDRESS_WIDTH - UNIT_OFFSET_LSB;

  typedef struct packed {
    pzcorebus_response_type             sresp;
    logic [MEMBUS_CONFIG.id_width-1:0]  sid;
    logic [UNITEN_COUNT_WIDTH-1:0]      uniten_offset;
    logic                               ignore_response;
  } pzcorebus_response_info;

  localparam  pzcorebus_config  BUS_CONFIG  = '{
    profile:              MEMBUS_CONFIG.profile,
    id_width:             MEMBUS_CONFIG.id_width,
    address_width:        MEMBUS_CONFIG.address_width,
    data_width:           MEMBUS_CONFIG.data_width,
    max_length:           MEMBUS_CONFIG.max_length,
    request_info_width:   MINFO_WIDTH,
    response_info_width:  MEMBUS_CONFIG.response_info_width,
    unit_data_width:      MEMBUS_CONFIG.unit_data_width,
    max_data_width:       MEMBUS_CONFIG.max_data_width
  };

  pzcorebus_if #(BUS_CONFIG)          membus_if();
  pzcorebus_if #(BUS_CONFIG)          slicer_if();
  pzcorebus_if #(CSRBUS_CONFIG)       csrbus_if();
  pzcorebus_command                   request_command;
  pzcorebus_sideband_info             sideband_info;
  logic                               info_fifo_empty;
  logic                               info_fifo_full;
  logic                               info_fifo_push;
  logic                               info_fifo_pop;
  pzcorebus_response_info [1:0]       response_info;
  logic                               response_count_empty;
  logic                               response_count_push;
  logic [1:0][LENGTH_COUNT_WIDTH-1:0] response_count;

//--------------------------------------------------------------
//  Slicer
//--------------------------------------------------------------
  always_comb begin
    membus_slave_if.scmd_accept = membus_if.scmd_accept;
    membus_if.mcmd_valid        = membus_slave_if.mcmd_valid;

    request_command       = membus_slave_if.get_command();
    request_command.info  = get_minfo(membus_slave_if.minfo, i_force_np_write, i_wait_for_all_responses);
    membus_if.put_command(request_command);
  end

  always_comb begin
    membus_slave_if.sdata_accept  = membus_if.sdata_accept;
    membus_if.mdata_valid         = membus_slave_if.mdata_valid;
    membus_if.put_write_data(membus_slave_if.get_write_data());
  end

  always_comb begin
    membus_if.mresp_accept      = membus_slave_if.mresp_accept;
    membus_slave_if.sresp_valid = membus_if.sresp_valid;
    membus_slave_if.put_response(membus_if.get_response());
  end

  function automatic logic [`PZCOREBUS_MAX_REQUEST_INFO_WIDTH-1:0] get_minfo(
    pzcorebus_request_info  minfo,
    logic                   force_np_write,
    logic                   wait_for_all_responses
  );
    pzcorebus_sideband_info info;
    info.force_np_write         = force_np_write;
    info.wait_for_all_responses = wait_for_all_responses;
    info.minfo                  = minfo;
    return (`PZCOREBUS_MAX_REQUEST_INFO_WIDTH)'(info);
  endfunction

  pzcorebus_slicer #(
    .BUS_CONFIG     (BUS_CONFIG       ),
    .REQUEST_VALID  (SLAVE_SLICER[0]  ),
    .RESPONSE_VALID (SLAVE_SLICER[1]  )
  ) u_slicer (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (membus_if  ),
    .master_if  (slicer_if  )
  );

//--------------------------------------------------------------
//  Request paht
//--------------------------------------------------------------
  if (1) begin : g_request_path
    logic                               busy;
    logic                               non_posted_ready;
    logic                               write_data_inactive;
    logic [1:0]                         read_valid;
    logic [2:0]                         write_valid;
    logic [1:0][LENGTH_COUNT_WIDTH-1:0] length_count;
    logic                               length_count_last;
    logic [1:0][DATA_COUNT_WIDTH-1:0]   data_count;
    logic                               data_count_last;
    logic [1:0][ADDRESS_WIDTH-1:0]      maddr;
    logic [LENGTH_COUNT_WIDTH-1:0]      request_count;
    logic [LENGTH_COUNT_WIDTH-1:0]      request_count_next;
    logic [1:0]                         update;

    always_comb begin
      sideband_info = pzcorebus_sideband_info'(slicer_if.minfo);
    end

    always_comb begin
      if (!busy) begin
        length_count[0] = slicer_if.get_length();
        data_count[0]   = slicer_if.maddr[UNIT_OFFSET_LSB+:UNIT_OFFSET_WIDTH];
        maddr[0]        = get_initial_maddr(slicer_if.maddr);
      end
      else begin
        length_count[0] = length_count[1];
        data_count[0]   = data_count[1];
        maddr[0]        = maddr[1];
      end

      length_count_last   = length_count[0] == LENGTH_COUNT_WIDTH'(1);
      data_count_last     = data_count[0]   == DATA_COUNT_WIDTH'(UNIT_SIZE - 1);
      request_count_next  = request_count + LENGTH_COUNT_WIDTH'(1);
      update[0]           = csrbus_if.command_ack();
      update[1]           = (write_valid == '1) && write_data_inactive;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        busy  <= '0;
      end
      else if (update != '0) begin
        if (length_count_last) begin
          busy  <= '0;
        end
        else begin
          busy  <= '1;
        end
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        length_count[1] <= LENGTH_COUNT_WIDTH'(0);
        data_count[1]   <= DATA_COUNT_WIDTH'(0);
        maddr[1]        <= ADDRESS_WIDTH'(0);
      end
      else if (update != '0) begin
        length_count[1] <= length_count[0] - LENGTH_COUNT_WIDTH'(1);
        data_count[1]   <= data_count[0] + DATA_COUNT_WIDTH'(1);
        maddr[1]        <= get_next_maddr(maddr[0]);
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        request_count <= LENGTH_COUNT_WIDTH'(0);
      end
      else if ((update != '0) && length_count_last) begin
        request_count <= LENGTH_COUNT_WIDTH'(0);
      end
      else if (update[0]) begin
        request_count <= request_count_next;
      end
    end

    always_comb begin
      csrbus_if.mcmd  = get_mcmd(slicer_if.mcmd, sideband_info);
      csrbus_if.mid   = '0;
      csrbus_if.maddr = maddr[0];
      csrbus_if.mdata = slicer_if.mdata[UNIT_WIDTH*data_count[0]+:UNIT_WIDTH];
      csrbus_if.minfo = sideband_info.minfo;

      non_posted_ready    = busy || (!info_fifo_full);
      write_data_inactive = slicer_if.mdata_byteen[UNIT_BYTE_SIZE*data_count[0]+:UNIT_BYTE_SIZE] == '0;
      read_valid[0]       = slicer_if.command_valid(PZCOREBUS_READ);
      read_valid[1]       = non_posted_ready;
      write_valid[0]      = slicer_if.command_with_data_valid();
      write_valid[1]      = slicer_if.mdata_valid;
      write_valid[2]      = csrbus_if.is_posted_command() || non_posted_ready;
      if (read_valid == '1) begin
        slicer_if.scmd_accept   = csrbus_if.scmd_accept && length_count_last;
        slicer_if.sdata_accept  = '0;
        csrbus_if.mcmd_valid    = '1;
      end
      else if (write_valid == '1) begin
        slicer_if.scmd_accept   = (csrbus_if.scmd_accept || write_data_inactive) && length_count_last;
        slicer_if.sdata_accept  = (csrbus_if.scmd_accept || write_data_inactive) && (data_count_last || length_count_last);
        csrbus_if.mcmd_valid    = !write_data_inactive;
      end
      else begin
        slicer_if.scmd_accept   = '0;
        slicer_if.sdata_accept  = '0;
        csrbus_if.mcmd_valid    = '0;
      end
    end

    always_comb begin
      csrbus_if.mlength       = '0;
      csrbus_if.mdata_valid   = '0;
      csrbus_if.mdata_byteen  = '0;
      csrbus_if.mdata_last    = '0;
    end

    always_comb begin
      info_fifo_push    = (update != '0) && csrbus_if.is_non_posted_command() && (!busy);
      response_info[0]  = get_response_info(slicer_if.mcmd, slicer_if.mid, slicer_if.maddr, sideband_info);
    end

    always_comb begin
      response_count_push = (update != '0) && csrbus_if.is_non_posted_command() && length_count_last;
      if (update[0]) begin
        response_count[0] = request_count_next;
      end
      else begin
        response_count[0] = request_count;
      end
    end
  end

  function automatic logic [CSRBUS_CONFIG.address_width-1:0] get_initial_maddr(
    logic [MEMBUS_CONFIG.address_width-1:0] maddr
  );
    logic [VALID_ADDRESS_WIDTH-1:0] initial_maddr;
    initial_maddr = {maddr[UNIT_OFFSET_LSB+:UNIT_ADDRESS_WIDTH], UNIT_OFFSET_LSB'(0)};
    return (CSRBUS_CONFIG.address_width)'(initial_maddr);
  endfunction

  function automatic logic [CSRBUS_CONFIG.address_width-1:0] get_next_maddr(
    logic [CSRBUS_CONFIG.address_width-1:0] maddr
  );
    logic [UNIT_ADDRESS_WIDTH-1:0]  base;
    logic [UNIT_ADDRESS_WIDTH-1:0]  maddr_next;
    base        = maddr[UNIT_OFFSET_LSB+:UNIT_ADDRESS_WIDTH];
    maddr_next  = base + UNIT_ADDRESS_WIDTH'(1);
    return {maddr_next, UNIT_OFFSET_LSB'(0)};
  endfunction

  function automatic pzcorebus_command_type get_mcmd(
    pzcorebus_command_type  mcmd,
    pzcorebus_sideband_info sideband_info
  );
    if (sideband_info.force_np_write && (mcmd == PZCOREBUS_WRITE)) begin
      return PZCOREBUS_WRITE_NON_POSTED;
    end
    else if (sideband_info.force_np_write && (mcmd == PZCOREBUS_FULL_WRITE)) begin
      return PZCOREBUS_FULL_WRITE_NON_POSTED;
    end
    else begin
      return mcmd;
    end
  endfunction

  function automatic pzcorebus_response_info get_response_info(
    pzcorebus_command_type                mcmd,
    logic [BUS_CONFIG.id_width-1:0]       mid,
    logic [BUS_CONFIG.address_width-1:0]  maddr,
    pzcorebus_sideband_info               sideband_info
  );
    pzcorebus_response_info info;

    info.sresp            = get_sresp(mcmd);
    info.sid              = mid;
    info.uniten_offset    = maddr[UNIT_OFFSET_LSB+:UNITEN_COUNT_WIDTH];
    info.ignore_response  = sideband_info.force_np_write && (mcmd inside {PZCOREBUS_WRITE, PZCOREBUS_FULL_WRITE});

    return info;
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

  pzbcm_fifo #(
    .WIDTH  (LENGTH_COUNT_WIDTH   ),
    .DEPTH  (RESPONSE_INFO_DEPTH  )
  ) u_response_count_fifo (
    .i_clk          (i_clk                ),
    .i_rst_n        (i_rst_n              ),
    .i_clear        ('0                   ),
    .o_empty        (response_count_empty ),
    .o_almost_full  (),
    .o_full         (),
    .o_word_count   (),
    .i_push         (response_count_push  ),
    .i_data         (response_count[0]    ),
    .i_pop          (info_fifo_pop        ),
    .o_data         (response_count[1]    )
  );

  if (1) begin : g_response_path
    logic [2:0]                         respons_done;
    logic                               busy;
    logic [1:0][LENGTH_COUNT_WIDTH-1:0] length_count;
    logic [LENGTH_COUNT_WIDTH-1:0]      length_count_next;
    logic [1:0][UNITEN_COUNT_WIDTH-1:0] uniten_end_count;
    logic [1:0][UNITEN_COUNT_WIDTH-1:0] uniten_start_count;
    logic [UNITEN_COUNT_WIDTH-1:0]      uniten_count_next;
    logic [DATA_COUNT_WIDTH-1:0]        data_count;
    logic                               data_count_last;
    logic [2:0]                         sresp_valid;
    logic [DATA_WIDTH-1:0]              sdata;
    logic                               serror;

    always_comb begin
      respons_done[0] = csrbus_if.response_ack() && sresp_valid[1];
      respons_done[1] = sresp_valid[2];
      respons_done[2] = (!response_count_empty) && (response_count[1] == LENGTH_COUNT_WIDTH'(0));
      info_fifo_pop   = respons_done != '0;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        busy  <= '0;
      end
      else if (respons_done != '0) begin
        busy  <= '0;
      end
      else if (csrbus_if.response_ack()) begin
        busy  <= '1;
      end
    end

    always_comb begin
      if (!busy) begin
        length_count[0]       = LENGTH_COUNT_WIDTH'(0);
        uniten_end_count[0]   = response_info[1].uniten_offset;
        uniten_start_count[0] = response_info[1].uniten_offset;
      end
      else begin
        length_count[0]       = length_count[1];
        uniten_end_count[0]   = uniten_end_count[1];
        uniten_start_count[0] = uniten_start_count[1];
      end

      length_count_next = length_count[0] + LENGTH_COUNT_WIDTH'(1);
      uniten_count_next = uniten_end_count[0] + UNITEN_COUNT_WIDTH'(1);
      data_count        = uniten_end_count[0][0+:DATA_COUNT_WIDTH];
      data_count_last   = data_count == '1;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        length_count[1]       <= LENGTH_COUNT_WIDTH'(0);
        uniten_end_count[1]   <= UNITEN_COUNT_WIDTH'(0);
        uniten_start_count[1] <= UNITEN_COUNT_WIDTH'(0);
      end
      else if (csrbus_if.response_ack()) begin
        length_count[1]     <= length_count_next;
        uniten_end_count[1] <= uniten_count_next;
        if (slicer_if.sresp_valid) begin
          uniten_start_count[1] <= uniten_count_next;
        end
      end
    end

    always_comb begin
      sresp_valid[0]  = (response_info[1].sresp == PZCOREBUS_RESPONSE_WITH_DATA) && data_count_last;
      sresp_valid[1]  = is_length_count_last(length_count_next, response_count_empty, response_count[1]);
      sresp_valid[2]  = is_length_count_last(length_count[0], response_count_empty, response_count[1]);

      if (info_fifo_empty) begin
        csrbus_if.mresp_accept  = '0;
        slicer_if.sresp_valid   = '0;
      end
      else if (response_info[1].ignore_response || (sresp_valid == '0)) begin
        csrbus_if.mresp_accept  = '1;
        slicer_if.sresp_valid   = '0;
      end
      else begin
        csrbus_if.mresp_accept  = slicer_if.mresp_accept;
        slicer_if.sresp_valid   = csrbus_if.sresp_valid || sresp_valid[2];
      end

      slicer_if.sresp         = response_info[1].sresp;
      slicer_if.sid           = response_info[1].sid;
      slicer_if.serror        = csrbus_if.serror || serror;
      slicer_if.sdata         = sdata;
      slicer_if.sinfo         = '0;
      slicer_if.sresp_uniten  = get_sresp_uniten(uniten_start_count[0], uniten_end_count[0]);
      slicer_if.sresp_last    = (sresp_valid[2:1] != '0) ? '1 : '0;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        serror  <= '0;
      end
      else if (slicer_if.response_ack() || (respons_done != '0)) begin
        serror  <= '0;
      end
      else if (csrbus_if.response_ack()) begin
        serror  <= slicer_if.serror;
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

  function automatic logic is_length_count_last(
    logic [LENGTH_COUNT_WIDTH-1:0]  length_count,
    logic                           response_count_empty,
    logic [LENGTH_COUNT_WIDTH-1:0]  response_count
  );
    return
      (!response_count_empty) && (response_count != LENGTH_COUNT_WIDTH'(0)) &&
      (length_count == response_count);
  endfunction

  function automatic logic [UNITEN_WIDTH-1:0] get_sresp_uniten(
    logic [UNITEN_COUNT_WIDTH-1:0]  start_count,
    logic [UNITEN_COUNT_WIDTH-1:0]  end_count
  );
    logic [UNITEN_WIDTH-1:0]  uniten;

    if (`pzcorebus_memoy_h_profile(MEMBUS_CONFIG)) begin
      for (int i = 0;i < UNITEN_WIDTH;++i) begin
        uniten[i] = UNITEN_COUNT_WIDTH'(i) inside {[start_count:end_count]};
      end
    end
    else begin
      uniten  = '0;
    end

    return uniten;
  endfunction

//--------------------------------------------------------------
//  Response buffer
//--------------------------------------------------------------
  pzcorebus_membus2csrbus_adapter_response_buffer #(
    .CSRBUS_CONFIG  (CSRBUS_CONFIG            ),
    .ENTRIES        (MAX_NON_POSTED_REQUESTS  ),
    .MASTER_SLICER  (MASTER_SLICER            )
  ) u_response_buffer (
    .i_clk                    (i_clk                                ),
    .i_rst_n                  (i_rst_n                              ),
    .i_base_id                (i_base_id                            ),
    .i_wait_for_all_responses (sideband_info.wait_for_all_responses ),
    .slave_if                 (csrbus_if                            ),
    .master_if                (csrbus_master_if                     )
  );
endmodule
