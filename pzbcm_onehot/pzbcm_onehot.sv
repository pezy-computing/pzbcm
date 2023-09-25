//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzbcm_onehot #(
  parameter int N = 1
);
  localparam  int BINARY_WIDTH  = (N >= 2) ? $clog2(N) : 1;

  function automatic logic [N-1:0] __onehot(
    int           n,
    int           step,
    logic [N-1:0] bits,
    logic [N-1:0] bits_reduced
  );
    int           next_n;
    logic [N-1:0] next_bits;
    logic [N-1:0] next_bits_reduced;

    next_n  = (n / 2) + (n % 2);
    for (int i = 0;i < next_n;++i) begin
      logic [1:0] or_bits;
      logic [1:0] or_result;

      if (((i + 1) == next_n) && ((n % 2) == 1)) begin
        or_bits = {1'b0, bits_reduced[2*i]};
      end
      else begin
        or_bits = bits_reduced[2*i+:2];
      end

      if (or_bits[0]) begin
        or_result = 2'b01;
      end
      else begin
        or_result = 2'b10;
      end

      next_bits_reduced[i]  = |or_bits;
      for (int j = 0;j < (2 * step);++j) begin
        int index = (2 * step * i) + j;
        if (index < N) begin
          next_bits[index]  = or_result[j/step] && bits[index];
        end
      end
    end

    if (next_n == 1) begin
      return next_bits;
    end
    else begin
      return __onehot(next_n, 2 * step, next_bits, next_bits_reduced);
    end
  endfunction

  function automatic logic [N-1:0] to_onehot(logic [N-1:0] bits);
    if (N > 1) begin
      return __onehot(N, 1, bits, bits);
    end
    else begin
      return bits;
    end
  endfunction

  function automatic logic [BINARY_WIDTH-1:0] to_binary(logic [N-1:0] bits);
    logic [BINARY_WIDTH-1:0]  binary;

    if (N >= 2) begin
      for (int i = 0;i < BINARY_WIDTH;++i) begin
        logic [N-1:0] temp;
        for (int j = 0;j < N;++j) begin
          temp[j] = bits[j] & j[i];
        end
        binary[i] = |temp;
      end
    end
    else begin
      binary  = BINARY_WIDTH'(0);
    end

    return binary;
  endfunction
endinterface
