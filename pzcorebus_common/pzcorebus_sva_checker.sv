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

  if (SVA_CHECKER) begin : g_mcmd
    pzcorebus_command mcmd;

    always_comb begin
      mcmd  = bus_if.get_command();
    end

    ast_keep_mcmd_until_acceptance:
    assert property (p_keep_mcmd_until_acceptance(
      i_clk, i_rst_n,
      bus_if.scmd_accept, bus_if.mcmd_valid, mcmd
    ))
    else
      $fatal(1, "mcmd is changed even though it is not accepted");
  end

  if (SVA_CHECKER && is_memory_profile(BUS_CONFIG)) begin : g_mdata
    pzcorebus_write_data  mdata;

    always_comb begin
      mdata = bus_if.get_write_data();
      for (int i = 0;i < (BUS_CONFIG.data_width / 8);++i) begin
        if (!mdata.byte_enable[i]) begin
          mdata.data[8*i+:8]  = '0;
        end
      end
    end

    ast_keep_mdata_until_acceptance:
    assert property (p_keep_mdata_until_acceptance(
      i_clk, i_rst_n,
      bus_if.sdata_accept, bus_if.mdata_valid, mdata
    ))
    else
      $fatal(1, "mdata is changed even though it is not accepted");
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
    ))
    else
      $fatal(1, "sresp is changed even though it is not accepted");

    if (is_memory_h_profile(BUS_CONFIG)) begin : g_sresp_last
      ast_sresp_last_should_not_be_0b01:
      assert property (p_sresp_last_should_not_be_0b01(
        i_clk, i_rst_n,
        bus_if.sresp_valid, sresp
      ))
      else
        $fatal(1, "invalid sresp_last is received");
    end
  end
endmodule
