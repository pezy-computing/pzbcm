//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_request_sva_checker
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG  = '0,
  parameter bit               SVA_CHECKER = 1
)(
  input var i_clk,
  input var i_rst_n,
  interface bus_if
);
  property p_keep_mcmd_until_acceptance (
    logic             clk,
    logic             rst_n,
    logic             scmd_accept,
    logic             mcmd_valid,
    pzcorebus_command mcmd
  );
    @(posedge clk) disable iff (!rst_n)
    (mcmd_valid && (!scmd_accept)) |=>
      ($stable(mcmd_valid) && $stable(mcmd));
  endproperty

  property p_keep_mdata_until_acceptance (
    logic                 clk,
    logic                 rst_n,
    logic                 sdata_accept,
    logic                 mdata_valid,
    pzcorebus_write_data  mdata
  );
    @(posedge clk) disable iff (!rst_n)
    (mdata_valid && (!sdata_accept)) |=>
      ($stable(mdata_valid) && $stable(mdata));
  endproperty

  let detect_ack(ack, id, wid) = (ack && (id == wid));

  property p_match_data_count_and_burst_length (
    logic         clk,
    logic         rst_n,
    logic         write_start,
    int unsigned  write_id,
    logic         mcmd_ack,
    int unsigned  mcmd_id,
    int unsigned  mburst_length,
    logic         mdata_last_ack,
    int unsigned  mdata_id,
    int unsigned  mdata_count
  );
    int unsigned  wid;
    int unsigned  burst_length;
    int unsigned  data_count;
    bit           result_0;
    bit           result_1;

    @(posedge clk) disable iff (!rst_n)
    (write_start, wid = write_id, burst_length = 0, data_count = 0, result_0 = 0, result_1 = 0) |->
      (
        first_match(
          (
            (detect_ack(mcmd_ack, mcmd_id, wid)[->1], burst_length = mburst_length) ##0
              detect_ack(mdata_last_ack, mdata_id, wid)[->1] ##0 (1, result_0 = ((mdata_count + 1) == burst_length))
          ) or (
            (detect_ack(mdata_last_ack, mdata_id, wid)[->1], data_count = (mdata_count + 1)) ##0
              detect_ack(mcmd_ack, mcmd_id, wid)[->1] ##0 (1, result_1 = (data_count == mburst_length))
          )
        ) ##0
        result_0 || result_1
      );
  endproperty

  if (SVA_CHECKER) begin : g_mcmd
    pzcorebus_command mcmd;

    always_comb begin
      mcmd  = bus_if.get_command();
    end

    ast_keep_mcmd_until_acceptance:
    assert property (p_keep_mcmd_until_acceptance(
      i_clk, i_rst_n,
      bus_if.scmd_accept, bus_if.mcmd_valid, mcmd
    ));
  end

  if (SVA_CHECKER && is_memory_profile(BUS_CONFIG)) begin : g_mdata
    pzcorebus_write_data  mdata;
    int unsigned          mburst_length;
    int unsigned          write_id;
    logic                 write_start;
    int unsigned          mcmd_id;
    logic                 mcmd_ack;
    int unsigned          mdata_id;
    logic                 mdata_ack;
    logic                 mdata_last_ack;
    int unsigned          mdata_count;

    always_comb begin
      mdata = bus_if.get_write_data();
      for (int i = 0;i < (BUS_CONFIG.data_width / 8);++i) begin
        if (!mdata.byte_enable[i]) begin
          mdata.data[8*i+:8]  = '0;
        end
      end
    end

    always_comb begin
      mburst_length = bus_if.get_burst_length();
    end

    always_comb begin
      mcmd_ack        = bus_if.command_with_data_ack();
      mdata_ack       = bus_if.write_data_ack();
      mdata_last_ack  = bus_if.write_data_last_ack();
    end

    always_comb begin
      write_start =
        (mcmd_ack && (mcmd_id == write_id)) ||
        (mdata_ack && (mdata_id == write_id));
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        write_id  <= 0;
        mcmd_id   <= 0;
        mdata_id  <= 0;
      end
      else begin
        if (write_start) begin
          write_id  <= write_id + 1;
        end
        if (mcmd_ack) begin
          mcmd_id <= mcmd_id + 1;
        end
        if (mdata_last_ack) begin
          mdata_id  <= mdata_id + 1;
        end
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        mdata_count <= 0;
      end
      else if (mdata_last_ack) begin
        mdata_count <= 0;
      end
      else if (mdata_ack) begin
        mdata_count <= mdata_count + 1;
      end
    end

    ast_keep_mdata_until_acceptance:
    assert property (p_keep_mdata_until_acceptance(
      i_clk, i_rst_n,
      bus_if.sdata_accept, bus_if.mdata_valid, mdata
    ));

    ast_match_data_count_and_burst_length:
    assert property (p_match_data_count_and_burst_length(
      i_clk, i_rst_n, write_start, write_id,
      mcmd_ack, mcmd_id, mburst_length,
      mdata_last_ack, mdata_id, mdata_count
    ));
  end
endmodule

module pzcorebus_request_sva_arary_checker
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG  = '0,
  parameter int               N           = 2,
  parameter bit               SVA_CHECKER = 1
)(
  input var i_clk,
  input var i_rst_n,
  interface bus_if[N]
);
  for (genvar i = 0;i < N;++i) begin : g
    pzcorebus_request_sva_checker #(
      .BUS_CONFIG   (BUS_CONFIG   ),
      .SVA_CHECKER  (SVA_CHECKER  )
    ) u_sva_checker (
      .i_clk    (i_clk      ),
      .i_rst_n  (i_rst_n    ),
      .bus_if   (bus_if[i]  )
    );
  end
endmodule

module pzcorebus_response_sva_checker
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG    = '0,
  parameter bit               SVA_CHECKER   = 1,
  parameter bit               SRESP_IF_ONLY = 1
)(
  input var i_clk,
  input var i_rst_n,
  interface bus_if
);
  localparam  int UNIT_BYTE       = BUS_CONFIG.unit_data_width / 8;
  localparam  int DATA_BYTE       = BUS_CONFIG.data_width / 8;
  localparam  int DATA_SIZE       = DATA_BYTE / UNIT_BYTE;
  localparam  int BURST_BOUNDARY  = BUS_CONFIG.response_boundary / DATA_BYTE;

  property p_keep_sresp_until_acceptance (
    logic               clk,
    logic               rst_n,
    logic               mresp_accept,
    logic               sresp_valid,
    pzcorebus_response  sresp
  );
    @(posedge clk) disable iff (!rst_n)
    (sresp_valid && (!mresp_accept)) |=>
      ($stable(sresp_valid) && $stable(sresp));
  endproperty

  property p_sresp_should_have_corresponting_mcmd(
    logic clk,
    logic rst_n,
    logic sresp_start,
    logic sresp_unknown
  );
    @(posedge clk) disable iff (!rst_n)
    (sresp_start) |-> !sresp_unknown;
  endproperty

  property p_match_sresp_count_and_burst_length(
    logic               clk,
    logic               rst_n,
    logic               sresp_start,
    logic               sresp_ack,
    pzcorebus_response  sresp,
    pzcorebus_command   mcmd
  );
    int unsigned  sresp_count;
    int unsigned  sresp_id;
    @(posedge clk) disable iff (!rst_n)
    (sresp_start, sresp_count = 0, sresp_id = sresp.id) |->
      first_match(
        (
          ((sresp_ack && (sresp.id == sresp_id))[->1], sresp_count += 1) ##0
            check_sresp_count(sresp_count, mcmd, sresp)
        )[*1:$] ##0 sresp.last[0]
      );
  endproperty

  function automatic logic check_sresp_count(
    int unsigned        sresp_count,
    pzcorebus_command   mcmd,
    pzcorebus_response  sresp
  );
    if (mcmd.command != PZCOREBUS_READ) begin
      return sresp.last[0] == 1;
    end
    else begin
      int last_count;

      if (is_memory_h_profile(BUS_CONFIG) && (sresp.last == 2'b10)) begin
        int unsigned  offset;
        offset  = (mcmd.address / DATA_BYTE) % BURST_BOUNDARY;
        if (((sresp_count + offset) % BURST_BOUNDARY) != 0) begin
          $display("sresp_count = %0d offset = %0d", sresp_count, offset);
          return 0;
        end
      end

      last_count  = calc_last_count(mcmd);
      if (sresp.last[0] == (sresp_count == last_count)) begin
        return 1;
      end
      else begin
        $display(
          "sresp_last = %b sresp_count = %0d last_count = %0d",
          sresp.last, sresp_count, last_count
        );
        return 0;
      end
    end
  endfunction

  function automatic int unsigned calc_last_count(
    pzcorebus_command mcmd
  );
    int unsigned  offset;
    int unsigned  unpacked_length;

    offset  = (mcmd.address % DATA_BYTE) / UNIT_BYTE;
    if (mcmd.length == 0) begin
      unpacked_length = BUS_CONFIG.max_length;
    end
    else begin
      unpacked_length = mcmd.length;
    end

    return (unpacked_length + offset + (DATA_SIZE - 1)) / DATA_SIZE;
  endfunction

  property p_sresp_last_should_not_be_0b01 (
    logic               clk,
    logic               rst_n,
    logic               sresp_valid,
    pzcorebus_response  sresp
  );
    @(posedge clk) disable iff (!rst_n)
    (sresp_valid) |-> (sresp.last != 2'b01);
  endproperty

  if (SVA_CHECKER) begin : g_sresp
    logic               sresp_ack;
    logic               sresp_last_ack;
    pzcorebus_response  sresp;

    always_comb begin
      sresp_ack       = bus_if.response_ack();
      sresp_last_ack  = bus_if.response_last_ack();
      sresp           = bus_if.get_response();
    end

    ast_keep_sresp_until_acceptance:
    assert property (p_keep_sresp_until_acceptance(
      i_clk, i_rst_n,
      bus_if.mresp_accept, bus_if.sresp_valid, sresp
    ));

    bit               sresp_busy[pzcorebus_response_type][int];
    bit               sresp_start;
    bit               sresp_unknown;
    pzcorebus_command mcmd;
    pzcorebus_command mcmd_queue[pzcorebus_response_type][int][$];

    if (!SRESP_IF_ONLY) begin : g_sresp_state
      always @(posedge i_clk, sresp_ack, sresp) begin
        if (!$isunknown(sresp)) begin
          sresp_start   = sresp_ack && (!sresp_busy[sresp.response][sresp.id]);
          sresp_unknown = sresp_start && (!mcmd_queue[sresp.response].exists(sresp.id));
        end
        else begin
          sresp_start   = '0;
          sresp_unknown = '0;
        end
      end

      always @(posedge i_clk, sresp_ack, sresp) begin
        if ((!$isunknown(sresp)) && mcmd_queue[sresp.response].exists(sresp.id)) begin
          mcmd  = mcmd_queue[sresp.response][sresp.id][0];
        end
      end

      always @(negedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          sresp_busy.delete();
        end
        else if (sresp_last_ack) begin
          sresp_busy[sresp.response].delete(sresp.id);
        end
        else if (sresp_start) begin
          sresp_busy[sresp.response][sresp.id]  = 1;
        end
      end

      always @(negedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          mcmd_queue.delete();
        end
        else begin
          if (bus_if.command_non_posted_ack()) begin
            case (bus_if.mcmd)
              PZCOREBUS_READ,
              PZCOREBUS_ATOMIC_NON_POSTED: begin
                mcmd_queue[PZCOREBUS_RESPONSE_WITH_DATA][bus_if.mid]
                  .push_back(bus_if.get_command());
              end
              default: begin
                mcmd_queue[PZCOREBUS_RESPONSE][bus_if.mid]
                  .push_back(bus_if.get_command());
              end
            endcase
          end
          if (sresp_last_ack) begin
            if (mcmd_queue[sresp.id].size() == 1) begin
              mcmd_queue[sresp.response].delete(sresp.id);
            end
            else begin
              void'(mcmd_queue[sresp.response][sresp.id].pop_front());
            end
          end
        end
      end
    end

    if (!SRESP_IF_ONLY) begin : g_sresp_unknown
      ast_sresp_should_have_corresponting_mcmd:
      assert property (p_sresp_should_have_corresponting_mcmd(
        i_clk, i_rst_n, sresp_start, sresp_unknown
      ));
    end

    if ((!SRESP_IF_ONLY) && is_memory_profile(BUS_CONFIG)) begin : g_sresp_count
      ast_match_sresp_count_and_burst_length:
      assert property (p_match_sresp_count_and_burst_length(
        i_clk, i_rst_n,
        sresp_start, sresp_ack, sresp, mcmd
      ));
    end

    if (is_memory_h_profile(BUS_CONFIG)) begin : g_sresp_last
      ast_sresp_last_should_not_be_0b01:
      assert property (p_sresp_last_should_not_be_0b01(
        i_clk, i_rst_n,
        bus_if.sresp_valid, sresp
      ));
    end
  end
endmodule

module pzcorebus_response_sva_array_checker
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG    = '0,
  parameter int               N             = 2,
  parameter bit               SVA_CHECKER   = 1,
  parameter bit               SRESP_IF_ONLY = 1
)(
  input var i_clk,
  input var i_rst_n,
  interface bus_if[N]
);
  for (genvar i = 0;i < N;++i) begin : g
    pzcorebus_response_sva_checker #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .SVA_CHECKER    (SVA_CHECKER    ),
      .SRESP_IF_ONLY  (SRESP_IF_ONLY  )
    ) u_sva_checker (
      .i_clk    (i_clk      ),
      .i_rst_n  (i_rst_n    ),
      .bus_if   (bus_if[i]  )
    );
  end
endmodule

module pzcorebus_sva_checker
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG            = '0,
  parameter pzcorebus_config  REQUEST_BUS_CONFIG    = BUS_CONFIG,
  parameter pzcorebus_config  RESPONSE_BUS_CONFIG   = BUS_CONFIG,
  parameter bit               SVA_CHECKER           = 1,
  parameter bit               REQUEST_SVA_CHECKER   = SVA_CHECKER,
  parameter bit               RESPONSE_SVA_CHECKER  = SVA_CHECKER
)(
  input var i_request_clk,
  input var i_request_rst_n,
  interface request_bus_if,
  input var i_response_clk,
  input var i_response_rst_n,
  interface response_bus_if
);
  if (REQUEST_SVA_CHECKER) begin : u_request
    pzcorebus_request_sva_checker #(
      .BUS_CONFIG (REQUEST_BUS_CONFIG )
    ) u_sva_checker (
      .i_clk    (i_request_clk    ),
      .i_rst_n  (i_request_rst_n  ),
      .bus_if   (request_bus_if   )
    );
  end

  if (RESPONSE_SVA_CHECKER) begin : g_response
    pzcorebus_response_sva_checker #(
      .BUS_CONFIG     (RESPONSE_BUS_CONFIG  ),
      .SRESP_IF_ONLY  (0                    )
    ) u_sva_checker (
      .i_clk    (i_response_clk   ),
      .i_rst_n  (i_response_rst_n ),
      .bus_if   (response_bus_if  )
    );
  end
endmodule
