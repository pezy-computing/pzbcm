//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_write_data_fifo
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG    = '0,
  parameter int               DEPTH         = 2,
  parameter int               THRESHOLD     = DEPTH,
  parameter bit               VALID         = 1,
  parameter bit               FLAG_FF_OUT   = 1,
  parameter bit               DATA_FF_OUT   = 1,
  parameter bit               RESET_DATA_FF = 1
)(
  input   var                 i_clk,
  input   var                 i_rst_n,
  input   var                 i_clear,
  output  var                 o_empty,
  output  var                 o_almost_full,
  output  var                 o_full,
  interface.write_data_slave  slave_if,
  interface.write_data_master master_if
);
  localparam  int WIDTH = get_packed_write_data_width(BUS_CONFIG, 1);

  logic [1:0]             sdata_accept;
  logic [1:0]             mdata_valid;
  logic [1:0][WIDTH-1:0]  mdata;

  always_comb begin
    slave_if.sdata_accept = sdata_accept[0];
    mdata_valid[0]        = slave_if.mdata_valid;
    mdata[0]              = slave_if.get_packed_write_data();
  end

  always_comb begin
    sdata_accept[1] = master_if.sdata_accept;
    master_if.mdata_valid = mdata_valid[1];
    master_if.put_packed_write_data(mdata[1]);
  end

  if (VALID && (DEPTH >= 2) && is_memory_profile(BUS_CONFIG)) begin : g
    logic empty;
    logic almost_full;
    logic full;

    always_comb begin
      o_empty       = empty;
      o_almost_full = almost_full;
      o_full        = full;
    end

    always_comb begin
      sdata_accept[0] = !full;
      mdata_valid[1]  = !empty;
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
      .i_push         (mdata_valid[0]   ),
      .i_data         (mdata[0]         ),
      .i_pop          (sdata_accept[1]  ),
      .o_data         (mdata[1]         )
    );
  end
  else begin : g
    always_comb begin
      o_empty       = '1;
      o_almost_full = '0;
      o_full        = '0;
    end

    always_comb begin
      sdata_accept[0] = sdata_accept[1];
      mdata_valid[1]  = mdata_valid[0];
      mdata[1]        = mdata[0];
    end
  end
endmodule
