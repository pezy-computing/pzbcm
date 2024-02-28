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

  let detect_ack(ack, id, wid) = ((ack && (id == wid))[->1]);

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
            (detect_ack(mcmd_ack, mcmd_id, wid), burst_length = mburst_length) ##0
              detect_ack(mdata_last_ack, mdata_id, wid) ##0 (1, result_0 = ((mdata_count + 1) == burst_length))
          ) or (
            (detect_ack(mdata_last_ack, mdata_id, wid), data_count = (mdata_count + 1)) ##0
              detect_ack(mcmd_ack, mcmd_id, wid) ##0 (1, result_1 = (data_count == mburst_length))
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

module pzcorebus_response_sva_checker
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG  = '0,
  parameter bit               SVA_CHECKER = 1
)(
  input var i_clk,
  input var i_rst_n,
  interface bus_if
);
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

  property p_sresp_last_should_not_be_0b01 (
    logic               clk,
    logic               rst_n,
    logic               sresp_valid,
    pzcorebus_response  sresp
  );
    @(posedge clk) disable iff (!rst_n)
    (sresp_valid) |->
      (sresp.last != 2'b01);
  endproperty

  if (SVA_CHECKER) begin : g_sresp
    pzcorebus_response  sresp;

    always_comb begin
      sresp = bus_if.get_response();
    end

    ast_keep_sresp_until_acceptance:
    assert property (p_keep_sresp_until_acceptance(
      i_clk, i_rst_n,
      bus_if.mresp_accept, bus_if.sresp_valid, sresp
    ));

    if (is_memory_h_profile(BUS_CONFIG)) begin : g_sresp_last
      ast_sresp_last_should_not_be_0b01:
      assert property (p_sresp_last_should_not_be_0b01(
        i_clk, i_rst_n,
        bus_if.sresp_valid, sresp
      ));
    end
  end
endmodule
