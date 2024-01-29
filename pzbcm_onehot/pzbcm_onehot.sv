//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzbcm_onehot #(
  parameter int N = 1
);
  localparam  int DEPTH         = $clog2(N);
  localparam  int REDUCER_WIDTH = (N >= 2) ? N         : 2;
  localparam  int BINARY_WIDTH  = (N >= 2) ? $clog2(N) : 1;

  function automatic logic [N-1:0] to_onehot(
    logic [N-1:0] bits
  );
    int                       step;
    int                       current_n;
    int                       next_n;
    logic [N-1:0]             current_bits;
    logic [N-1:0]             next_bits;
    logic [REDUCER_WIDTH-1:0] current_reducer;
    logic [REDUCER_WIDTH-1:0] next_reducer;

    for (int i = 0;i < DEPTH;++i) begin
      if (i == 0) begin
        current_n       = N;
        current_bits    = bits;
        current_reducer = REDUCER_WIDTH'(bits);
      end
      else begin
        current_n       = next_n;
        current_bits    = next_bits;
        current_reducer = next_reducer;
      end

      next_n  = (current_n / 2) + (current_n % 2);
      step    = 2**i;
      for (int j = 0;j < next_n;++j) begin
        logic [1:0] or_bits;
        logic [1:0] or_result;

        if (((j + 1) == next_n) && (((current_n % 2) == 1))) begin
          or_bits = 2'(current_reducer[2*j]);
        end
        else begin
          or_bits = current_reducer[2*j+:2];
        end

        if (or_bits[0]) begin
          or_result = 2'b01;
        end
        else begin
          or_result = 2'b10;
        end

        next_reducer[j] = |or_bits;
        for (int k = 0;k < (2 * step);++k) begin
          int index = 2 * step * j + k;
          if (index < N) begin
            next_bits[index]  = or_result[k/step] && current_bits[index];
          end
        end
      end
    end

    if (N > 1) begin
      return next_bits;
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
