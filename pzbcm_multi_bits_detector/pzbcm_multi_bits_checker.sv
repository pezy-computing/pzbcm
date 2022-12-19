//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
interface pzbcm_multi_bits_checker #(
  parameter int N = 2
);
  localparam  int INDEX_WIDTH = $clog2(N + 1);

  function automatic logic [1:0] reduce_to_2bits(
    logic [N-1:0]           bits,
    logic [INDEX_WIDTH-1:0] n
  );
    if (n > 2) begin
      logic [INDEX_WIDTH-1:0] half_n;
      logic [1:0]             result[2];

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

        result[i] = reduce_to_2bits(next_bits, next_n);
      end

      return marge_result(result);
    end
    else if (n == 2) begin
      return bits[1:0];
    end
    else begin
      return {1'b0, bits[0]};
    end
  endfunction

  function automatic logic [1:0] marge_result(logic [1:0] result[2]);
    if ((result[0] != 2'b00) && (result[1] != 2'b00)) begin
      return 2'b11;
    end
    else begin
      return result[0] | result[1];
    end
  endfunction

  function automatic logic is_multi_bits(logic [N-1:0] bits);
    if (N >= 2) begin
      return (reduce_to_2bits(bits, INDEX_WIDTH'(N)) == 2'b11);
    end
    else begin
      return '0;
    end
  endfunction
endinterface
