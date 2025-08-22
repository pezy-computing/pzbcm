//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzbcm_ram #(
  parameter int                         WORD_SIZE     = 1,
  parameter int                         ADDRESS_WIDTH = (WORD_SIZE >= 2) ? $clog2(WORD_SIZE) : 1,
  parameter int                         DATA_WIDTH    = 8,
  parameter type                        DATA_TYPE     = logic [DATA_WIDTH-1:0],
  parameter bit                         BUFFER_OUT    = 0,
  parameter bit                         USE_RESET     = 0,
  parameter bit [$bits(DATA_TYPE)-1:0]  INITIAL_VALUE = '0
)(
  input   var                     i_clk,
  input   var                     i_rst_n,
  input   var                     i_clr,
  input   var                     i_mea,
  input   var                     i_wea,
  input   var [ADDRESS_WIDTH-1:0] i_adra,
  input   var DATA_TYPE           i_da,
  input   var                     i_meb,
  input   var [ADDRESS_WIDTH-1:0] i_adrb,
  output  var DATA_TYPE           o_qb
);
  logic [$bits(DATA_TYPE)-1:0]  ram[WORD_SIZE];
  logic [$bits(DATA_TYPE)-1:0]  q;

  if (USE_RESET) begin : g_ram
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        ram <= '{default: INITIAL_VALUE};
      end
      else if (i_clr) begin
        ram <= '{default: INITIAL_VALUE};
      end
      else if (i_mea && i_wea) begin
        ram[i_adra] <= i_da;
      end
    end
  end
  else begin : g_ram
    always_ff @(posedge i_clk) begin
      if (i_mea && i_wea) begin
        ram[i_adra] <= i_da;
      end
    end
  end

  always_comb begin
    o_qb  = DATA_TYPE'(q);
  end

  if (!BUFFER_OUT) begin : g_out
    always_comb begin
      q = ram[i_adrb];
    end
  end
  else if (USE_RESET) begin : g_out
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        q <= INITIAL_VALUE;
      end
      else if (i_clr) begin
        q <= INITIAL_VALUE;
      end
      else if (i_meb) begin
        q <= ram[i_adrb];
      end
    end
  end
  else begin : g_out
    always_ff @(posedge i_clk) begin
      if (i_meb) begin
        q <= ram[i_adrb];
      end
    end
  end
endmodule
