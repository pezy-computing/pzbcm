//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_response_fifo
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG          = '0,
  parameter int               RESPONSE_DEPTH      = 2,
  parameter int               RESPONSE_THRESHOLD  = RESPONSE_DEPTH,
  parameter bit               RESPONSE_VALID      = 1,
  parameter bit               FLAG_FF_OUT         = 1,
  parameter bit               DATA_FF_OUT         = 1
)(
  input   var               i_clk,
  input   var               i_rst_n,
  input   var               i_clear,
  output  var               o_empty,
  output  var               o_almost_full,
  output  var               o_full,
  interface.response_slave  slave_if,
  interface.response_master master_if
);
  localparam  int PACKED_RESPONSE_WIDTH   = get_packed_response_width(BUS_CONFIG);

  typedef logic [PACKED_RESPONSE_WIDTH-1:0]   pzcorebus_packed_response;

  logic                     empty;
  logic                     almost_full;
  logic                     full;
  logic                     sresp_valid;
  pzcorebus_packed_response slave_sresp;
  logic                     mresp_accept;
  pzcorebus_packed_response master_sresp;

  always_comb begin
    o_empty       = empty;
    o_almost_full = almost_full;
    o_full        = full;
  end

  always_comb begin
    slave_if.sresp_valid  = sresp_valid;
    slave_if.put_packed_response(slave_sresp);
  end

  always_comb begin
    master_if.mresp_accept  = mresp_accept;
    master_sresp            = master_if.get_packed_response();
  end

  if (RESPONSE_VALID && (RESPONSE_DEPTH >= 1)) begin : g_response
    pzbcm_fifo #(
      .WIDTH        (PACKED_RESPONSE_WIDTH  ),
      .DEPTH        (RESPONSE_DEPTH         ),
      .THRESHOLD    (RESPONSE_THRESHOLD     ),
      .FLAG_FF_OUT  (FLAG_FF_OUT            ),
      .DATA_FF_OUT  (DATA_FF_OUT            )
    ) u_fifo (
      .i_clk          (i_clk                  ),
      .i_rst_n        (i_rst_n                ),
      .i_clear        (i_clear                ),
      .o_empty        (empty                  ),
      .o_almost_full  (almost_full            ),
      .o_full         (full                   ),
      .o_word_count   (),
      .i_push         (master_if.sresp_valid  ),
      .i_data         (master_sresp           ),
      .i_pop          (slave_if.mresp_accept  ),
      .o_data         (slave_sresp            )
    );

    always_comb begin
      mresp_accept  = !full;
      sresp_valid   = !empty;
    end
  end
  else begin : g_response
    always_comb begin
      empty       = '1;
      almost_full = '0;
      full        = '0;
    end

    always_comb begin
      mresp_accept  = slave_if.mresp_accept;
      sresp_valid   = master_if.sresp_valid;
      slave_sresp   = master_sresp;
    end
  end
endmodule
