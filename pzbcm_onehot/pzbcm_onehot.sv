//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
interface pzbcm_onehot #(
  parameter int N = 1
);
  localparam  int INDEX_WIDTH   = $clog2(N + 1);
  localparam  int BINARY_WIDTH  = (N >= 2) ? $clog2(N) : 1;

  function automatic logic [N-1:0] __onehot(
    logic [N-1:0]           bits,
    logic [INDEX_WIDTH-1:0] n
  );
    if (n > 2) begin
      logic [INDEX_WIDTH-1:0] half_n;
      logic [N-1:0]           half_result[2];

      half_n  = INDEX_WIDTH'(n[INDEX_WIDTH-1:1]);
      for (int i = 0;i < 2;++i) begin
        logic [N-1:0]           next_bits;
        logic [INDEX_WIDTH-1:0] next_n;

        next_n  = ((i == 1) && n[0]) ? half_n + INDEX_WIDTH'(1) : half_n;
        for (int j = 0;j < next_n;++j) begin
          if (i == 0) begin
            next_bits[j]  = bits[j];
          end
          else begin
            next_bits[j]  = bits[j+half_n];
          end
        end

        half_result[i]  = __onehot(next_bits, next_n);
      end

      return marge_result(half_result, n, half_n);
    end
    else if (n == 2) begin
      logic [N-1:0] result;

      result  = bits;
      if (bits[1:0] != 2'b10) begin
        result[1] = '0;
      end

      return result;
    end
    else begin
      return bits;
    end
  endfunction

  function automatic logic [N-1:0] marge_result(
    logic [N-1:0]           result[2],
    logic [INDEX_WIDTH-1:0] n,
    logic [INDEX_WIDTH-1:0] half_n
  );
    logic [1:0]   ored;
    logic [N-1:0] marged_result;

    ored  = '0;
    for (int i = 0;i < n;++i) begin
      if (i < half_n) begin
        ored[0] |= result[0][i];
      end
      else begin
        ored[1] |= result[1][i-half_n];
      end
    end

    if (ored == 2'b10) begin
      for (int i = 0;i < n;++i) begin
        if (i < half_n) begin
          marged_result[i]  = '0;
        end
        else begin
          marged_result[i]  = result[1][i-half_n];
        end
      end
    end
    else begin
      for (int i = 0;i < n;++i) begin
        if (i < half_n) begin
          marged_result[i]  = result[0][i];
        end
        else begin
          marged_result[i]  = '0;
        end
      end
    end

    return marged_result;
  endfunction

  function automatic logic [N-1:0] to_onehot(logic [N-1:0] bits);
    return __onehot(bits, INDEX_WIDTH'(N));
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
