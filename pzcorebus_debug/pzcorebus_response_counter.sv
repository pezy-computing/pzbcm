//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_response_counter
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG      = '0,
  parameter int               WIDTH           = 16,
  parameter bit [1:0]         TARGET_RESPONSE = '1,
  parameter bit               ERROR_ONLY      = 0,
  parameter bit               LAST_ONLY       = 0
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_enable,
  input   var             i_clear,
  pzcorebus_if.monitor    corebus_if,
  output  var [WIDTH-1:0] o_count
);
  logic [WIDTH-1:0] count;
  logic             hit_response;

  always_comb begin
    o_count = count;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      count <= '0;
    end
    else if (i_clear) begin
      count <= '0;
    end
    else if (i_enable && hit_response) begin
      count <= count + WIDTH'(1);
    end
  end

  always_comb begin
    hit_response  =
      corebus_if.response_ack() &&
      is_target_response(corebus_if.sresp, corebus_if.serror, corebus_if.sresp_last[0]);
  end

  function automatic logic is_target_response(
    pzcorebus_response_type sresp,
    logic                   serror,
    logic                   sresp_last
  );
    logic target_response;

    case (sresp)
      PZCOREBUS_RESPONSE:           target_response = TARGET_RESPONSE[0];
      PZCOREBUS_RESPONSE_WITH_DATA: target_response = TARGET_RESPONSE[1];
      default:                      target_response = '0;
    endcase

    return
      target_response &&
      ((!ERROR_ONLY) || serror) && ((!LAST_ONLY) || sresp_last);
  endfunction
endmodule
