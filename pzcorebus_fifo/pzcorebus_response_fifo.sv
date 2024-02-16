//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_response_fifo
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG    = '0,
  parameter int               DEPTH         = 2,
  parameter int               THRESHOLD     = DEPTH,
  parameter bit               VALID         = 1,
  parameter bit               FLAG_FF_OUT   = 1,
  parameter bit               DATA_FF_OUT   = 1,
  parameter bit               RESET_DATA_FF = 1,
  parameter bit               SVA_CHECKER   = 1
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
  localparam  int WIDTH = get_packed_response_width(BUS_CONFIG);

  logic [1:0]             mresp_accept;
  logic [1:0]             sresp_valid;
  logic [1:0][WIDTH-1:0]  sresp;

  always_comb begin
    master_if.mresp_accept  = mresp_accept[0];
    sresp_valid[0]          = master_if.sresp_valid;
    sresp[0]                = master_if.get_packed_response();
  end

  always_comb begin
    mresp_accept[1]       = slave_if.mresp_accept;
    slave_if.sresp_valid  = sresp_valid[1];
    slave_if.put_packed_response(sresp[1]);
  end

  if (VALID && (DEPTH >= 1)) begin : g
    logic empty;
    logic almost_full;
    logic full;

    always_comb begin
      o_empty       = empty;
      o_almost_full = almost_full;
      o_full        = full;
    end

    always_comb begin
      mresp_accept[0] = !full;
      sresp_valid[1]  = !empty;
    end

    pzbcm_fifo #(
      .WIDTH          (WIDTH          ),
      .DEPTH          (DEPTH          ),
      .THRESHOLD      (THRESHOLD      ),
      .FLAG_FF_OUT    (FLAG_FF_OUT    ),
      .DATA_FF_OUT    (DATA_FF_OUT    ),
      .RESET_DATA_FF  (RESET_DATA_FF  )
    ) u_fifo (
      .i_clk          (i_clk            ),
      .i_rst_n        (i_rst_n          ),
      .i_clear        (i_clear          ),
      .o_empty        (empty            ),
      .o_almost_full  (almost_full      ),
      .o_full         (full             ),
      .o_word_count   (),
      .i_push         (sresp_valid[0]   ),
      .i_data         (sresp[0]         ),
      .i_pop          (mresp_accept[1]  ),
      .o_data         (sresp[1]         )
    );
  end
  else begin : g_response
    always_comb begin
      o_empty       = '1;
      o_almost_full = '0;
      o_full        = '0;
    end

    always_comb begin
      mresp_accept[0] = mresp_accept[1];
      sresp_valid[1]  = sresp_valid[0];
      sresp[1]        = sresp[0];
    end
  end

//--------------------------------------------------------------
//  SVA checker
//--------------------------------------------------------------
  if (PZCOREBUS_ENABLE_SVA_CHECKER) begin : g_sva
    pzcorebus_response_sva_checker #(
      .BUS_CONFIG   (BUS_CONFIG   ),
      .SVA_CHECKER  (SVA_CHECKER  )
    ) u_sva_checker (
      .i_clk    (i_clk      ),
      .i_rst_n  (i_rst_n    ),
      .bus_if   (master_if  )
    );
  end
endmodule
