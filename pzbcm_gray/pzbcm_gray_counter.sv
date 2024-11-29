//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_gray_counter #(
  parameter int MAX_COUNT = 3,
  parameter int WIDTH     = $clog2(MAX_COUNT)
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_clear,
  input   var             i_set,
  input   var [WIDTH-1:0] i_set_value,
  input   var             i_up,
  output  var [WIDTH-1:0] o_gray_count
);
  localparam  int             FIT_POW_2   = MAX_COUNT == ((2**WIDTH) - 1);
  localparam  bit [WIDTH-1:0] LAST_COUNT  = MAX_COUNT ^ (MAX_COUNT >> 1);

  logic [WIDTH-1:0] count;
  logic [WIDTH-1:0] count_next;

  always_comb begin
    o_gray_count  = count;
  end

  always_comb begin
    count_next  = calc_count_next(count);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      count <= WIDTH'(0);
    end
    else if (i_clear) begin
      count <= WIDTH'(0);
    end
    else if (i_set) begin
      count <= i_set_value;
    end
    else if (i_up) begin
      if (FIT_POW_2 || (count != LAST_COUNT)) begin
        count <= count_next;
      end
      else begin
        count <= WIDTH'(0);
      end
    end
  end

  function automatic logic [WIDTH-1:0] calc_count_next(
    logic [WIDTH-1:0] count
  );
    logic [WIDTH-1:0] parity;
    logic [WIDTH-1:0] next;
    logic             cin;
    logic             cout;

    parity[WIDTH-1] = '0;
    for (int i = WIDTH - 2;i >= 0;--i) begin
      parity[i] = parity[i+1] ^ count[i+1];
    end

    cout  = '1;
    for (int i = 0;i < WIDTH;++i) begin
      cin = cout;
      if (!cin) begin
        next[i] = count[i];
        cout    = '0;
      end
      else if ((i + 1) == WIDTH) begin
        next[i] = !count[i];
        cout    = '0;
      end
      else begin
        next[i] = !parity[i];
        cout    = count[i] != parity[i];
      end
    end

    return next;
  endfunction

`ifndef SYNTHESIS
  bit [WIDTH-1:0] count_binary;
  bit [WIDTH-1:0] count_ungray;

  pzbcm_gray #(WIDTH) u_gray();
  always_comb begin
    count_ungray  = u_gray.decode(count);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      count_binary  <= WIDTH'(0);
    end
    else if (i_clear) begin
      count_binary  <= WIDTH'(0);
    end
    else if (i_set) begin
      count_binary  <= u_gray.decode(i_set_value);
    end
    else if (i_up) begin
      if (count_binary == MAX_COUNT) begin
        count_binary  <= WIDTH'(0);
      end
      else begin
        count_binary  <= count_binary + 1;
      end
    end
  end

  property p_match_count;
    @(posedge i_clk) disable iff (!i_rst_n)
    count_binary == count_ungray;
  endproperty

  ast_match_count:
  assert property(p_match_count);
`endif
endmodule
