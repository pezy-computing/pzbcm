//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_command_fifo
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG  = '0,
  parameter int               DEPTH       = 2,
  parameter int               THRESHOLD   = DEPTH,
  parameter bit               VALID       = 1,
  parameter bit               FLAG_FF_OUT = 1,
  parameter bit               DATA_FF_OUT = 1
)(
  input   var               i_clk,
  input   var               i_rst_n,
  input   var               i_clear,
  output  var               o_empty,
  output  var               o_almost_full,
  output  var               o_full,
  interface.command_slave   slave_if,
  interface.command_master  master_if
);
  parameter int WIDTH = get_packed_command_width(BUS_CONFIG);

  logic [1:0]             scmd_accept;
  logic [1:0]             mcmd_valid;
  logic [1:0][WIDTH-1:0]  mcmd;

  always_comb begin
    slave_if.scmd_accept  = scmd_accept[0];
    mcmd_valid[0]         = slave_if.mcmd_valid;
    mcmd[0]               = slave_if.get_packed_command();
  end

  always_comb begin
    scmd_accept[1]        = master_if.scmd_accept;
    master_if.mcmd_valid  = mcmd_valid[1];
    master_if.put_packed_command(mcmd[1]);
  end

  if (VALID && (DEPTH >= 2)) begin : g
    logic empty;
    logic almost_full;
    logic full;

    always_comb begin
      o_empty       = empty;
      o_almost_full = almost_full;
      o_full        = full;
    end

    always_comb begin
      scmd_accept[0]  = !full;
      mcmd_valid[1]   = !empty;
    end

    pzbcm_fifo #(
      .WIDTH        (WIDTH        ),
      .DEPTH        (DEPTH        ),
      .THRESHOLD    (THRESHOLD    ),
      .FLAG_FF_OUT  (FLAG_FF_OUT  ),
      .DATA_FF_OUT  (DATA_FF_OUT  )
    ) u_fifo (
      .i_clk          (i_clk          ),
      .i_rst_n        (i_rst_n        ),
      .i_clear        (i_clear        ),
      .o_empty        (empty          ),
      .o_almost_full  (almost_full    ),
      .o_full         (full           ),
      .o_word_count   (),
      .i_push         (mcmd_valid[0]  ),
      .i_data         (mcmd[0]        ),
      .i_pop          (scmd_accept[1] ),
      .o_data         (mcmd[1]        )
    );
  end
  else begin : g
    always_comb begin
      o_empty       = '1;
      o_almost_full = '0;
      o_full        = '0;
    end

    always_comb begin
      scmd_accept[0]  = scmd_accept[1];
      mcmd_valid[1]   = mcmd_valid[0];
      mcmd[1]         = mcmd[0];
    end
  end
endmodule
