//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzbcm_async_fifo
  import  pzbcm_async_fifo_pkg::calc_default_depth;
#(
  parameter int   WIDTH               = 8,
  parameter type  TYPE                = logic [WIDTH-1:0],
  parameter int   STAGES              = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES,
  parameter int   DEPTH               = calc_default_depth(STAGES),
  parameter int   THRESHOLD           = DEPTH,
  parameter bit   USE_OUT_DATA_RESET  = '0,
  parameter TYPE  INITIAL_OUT_DATA    = TYPE'(0)
)(
  input   var       is_clk,
  input   var       is_rst_n,
  output  var       os_almost_full,
  output  var       os_full,
  input   var       is_push,
  input   var TYPE  is_data,
  input   var       id_clk,
  input   var       id_rst_n,
  output  var       od_empty,
  input   var       id_pop,
  output  var TYPE  od_data
);
  initial begin
    assume (DEPTH == (2**$clog2(DEPTH)));
  end

  localparam  int POINTER_WIDTH = $clog2(DEPTH) + 1;

  logic [POINTER_WIDTH-1:0] wp_sclk;
  logic [POINTER_WIDTH-1:0] wp_sclk_next;
  logic [POINTER_WIDTH-1:0] wp_sclk_gray;
  logic [POINTER_WIDTH-1:0] rp_sclk;
  logic [POINTER_WIDTH-1:0] rp_sclk_gray;
  logic [POINTER_WIDTH-1:0] wp_dclk;
  logic [POINTER_WIDTH-1:0] wp_dclk_gray;
  logic [POINTER_WIDTH-1:0] rp_dclk;
  logic [POINTER_WIDTH-1:0] rp_dclk_next;
  logic [POINTER_WIDTH-1:0] rp_dclk_gray;

//--------------------------------------------------------------
//  Utility
//--------------------------------------------------------------
  pzbcm_gray #(POINTER_WIDTH) u_gray();

//--------------------------------------------------------------
//  FIFO Control (Write Side)
//--------------------------------------------------------------
  logic [POINTER_WIDTH-1:0] word_count;
  logic                     almost_full;
  logic                     full;
  logic                     push;

  always_comb begin
    os_almost_full  = almost_full;
    os_full         = full;
  end

  always_comb begin
    push  = (!full) ? is_push : '0;
  end

  always_comb begin
    word_count  = wp_sclk_next - rp_sclk;
  end

  always_ff @(posedge is_clk, negedge is_rst_n) begin
    if (!is_rst_n) begin
      almost_full <= '0;
      full        <= '0;
    end
    else begin
      almost_full <= (word_count >= POINTER_WIDTH'(THRESHOLD));
      full        <= word_count[POINTER_WIDTH-1];
    end
  end

  always_comb begin
    if (push) begin
      wp_sclk_next  = wp_sclk + POINTER_WIDTH'(1);
    end
    else begin
      wp_sclk_next  = wp_sclk;
    end
  end

  always_ff @(posedge is_clk, negedge is_rst_n) begin
    if (!is_rst_n) begin
      wp_sclk <= POINTER_WIDTH'(0);
    end
    else begin
      wp_sclk <= wp_sclk_next;
    end
  end

  always_ff @(posedge is_clk, negedge is_rst_n) begin
    if (!is_rst_n) begin
      wp_sclk_gray  <= POINTER_WIDTH'(0);
    end
    else begin
      wp_sclk_gray  <= u_gray.encode(wp_sclk);
    end
  end

  always_comb begin
    rp_sclk = u_gray.decode(rp_sclk_gray);
  end

//--------------------------------------------------------------
//  FIFO Control (Read Side)
//--------------------------------------------------------------
  logic empty;
  logic empty_next;
  logic pop;

  always_comb begin
    od_empty  = empty;
  end

  always_comb begin
    if (pop) begin
      empty_next  = wp_dclk == rp_dclk_next;
    end
    else begin
      empty_next  = wp_dclk == rp_dclk;
    end
  end

  always_ff @(posedge id_clk, negedge id_rst_n) begin
    if (!id_rst_n) begin
      empty <= '1;
    end
    else begin
      empty <= empty_next;
    end
  end

  always_comb begin
    pop = (!empty) ? id_pop : '0;
  end

  always_ff @(posedge id_clk, negedge id_rst_n) begin
    if (!id_rst_n) begin
      rp_dclk       <= POINTER_WIDTH'(0);
      rp_dclk_next  <= POINTER_WIDTH'(1);
    end
    else if (pop) begin
      rp_dclk       <= rp_dclk_next;
      rp_dclk_next  <= rp_dclk_next + POINTER_WIDTH'(1);
    end
  end

  always_ff @(posedge id_clk, negedge id_rst_n) begin
    if (!id_rst_n) begin
      rp_dclk_gray  <= POINTER_WIDTH'(0);
    end
    else begin
      rp_dclk_gray  <= u_gray.encode(rp_dclk);
    end
  end

  always_comb begin
    wp_dclk = u_gray.decode(wp_dclk_gray);
  end

//--------------------------------------------------------------
//  Synchronizer
//--------------------------------------------------------------
  pzbcm_synchronizer #(
    .WIDTH  (POINTER_WIDTH  ),
    .STAGES (STAGES         )
  ) u_synchronizer_wp (
    .i_clk    (id_clk       ),
    .i_rst_n  (id_rst_n     ),
    .i_d      (wp_sclk_gray ),
    .o_d      (wp_dclk_gray )
  );

  pzbcm_synchronizer #(
    .WIDTH  (POINTER_WIDTH  ),
    .STAGES (STAGES         )
  ) u_synchronizer_rp (
    .i_clk    (is_clk       ),
    .i_rst_n  (is_rst_n     ),
    .i_d      (rp_dclk_gray ),
    .o_d      (rp_sclk_gray )
  );

  logic [$bits(TYPE)-1:0] ram[DEPTH];
  logic [$bits(TYPE)-1:0] q;

  always_ff @(posedge is_clk) begin
    if (push) begin
      ram[wp_sclk[POINTER_WIDTH-2:0]] <= is_data;
    end
  end

  if (USE_OUT_DATA_RESET) begin : g_q
    always_ff @(posedge id_clk, negedge id_rst_n) begin
      if (!id_rst_n) begin
        q <= INITIAL_OUT_DATA;
      end
      else if (empty && (!empty_next)) begin
        q <= ram[rp_dclk[POINTER_WIDTH-2:0]];
      end
      else if (pop && (!empty_next)) begin
        q <= ram[rp_dclk_next[POINTER_WIDTH-2:0]];
      end
    end
  end
  else begin : g_q
    always_ff @(posedge id_clk) begin
      if (empty && (!empty_next)) begin
        q <= ram[rp_dclk[POINTER_WIDTH-2:0]];
      end
      else if (pop && (!empty_next)) begin
        q <= ram[rp_dclk_next[POINTER_WIDTH-2:0]];
      end
    end
  end

  always_comb begin
    od_data = TYPE'(q);
  end
endmodule
