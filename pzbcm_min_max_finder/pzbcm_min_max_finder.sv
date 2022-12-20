//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzbcm_min_max_finder #(
  parameter int   ENTRIES       = 1,
  parameter int   WIDTH         = 1,
  parameter type  TYPE          = logic [WIDTH-1:0],
  parameter type  RESULT        = logic,
  parameter int   COMPARE_WIDTH = $bits(TYPE)
);
  function automatic logic [1:0] __do_compare(
    bit   compare_min,
    TYPE  lhs,
    TYPE  rhs
  );
    logic result;

    if (compare_min) begin
      result  = lhs[0+:COMPARE_WIDTH] <= rhs[0+:COMPARE_WIDTH];
    end
    else begin
      result  = lhs[0+:COMPARE_WIDTH] >= rhs[0+:COMPARE_WIDTH];
    end

    return (result) ? 2'b01 : 2'b10;
  endfunction

  function automatic RESULT __find_min_max(
    bit                 compare_min,
    int                 n,
    int                 step,
    TYPE  [ENTRIES-1:0] data,
    logic [ENTRIES-1:0] location
  );
    int                 next_n;
    TYPE  [ENTRIES-1:0] next_data;
    logic [ENTRIES-1:0] next_location;
    logic [1:0]         compare_result;

    next_n  = (n / 2) + (n % 2);
    for (int i = 0;i < next_n;++i) begin
      if (((i + 1) == next_n) && ((n % 2) == 1)) begin
        compare_result  = 2'b01;
      end
      else begin
        compare_result  = __do_compare(compare_min, data[2*i+0], data[2*i+1]);
      end

      if (compare_result == 2'b01) begin
        next_data[i]  = data[2*i+0];
      end
      else begin
        next_data[i]  = data[2*i+1];
      end

      for (int j = 0;j < (2 * step);++j) begin
        if (((2 * step * i) + j) < ENTRIES) begin
          next_location[2*step*i+j] = compare_result[j/step] && location[2*step*i+j];
        end
      end
    end

    if (next_n == 1) begin
      RESULT  result;
      result.data     = next_data[0];
      result.location = next_location;
      return result;
    end
    else begin
      return __find_min_max(compare_min, next_n, 2 * step, next_data, next_location);
    end
  endfunction

  function automatic RESULT find_min(
    TYPE  [ENTRIES-1:0] data
  );
    return __find_min_max(1, ENTRIES, 1, data, '1);
  endfunction

  function automatic RESULT find_max(
    TYPE  [ENTRIES-1:0] data
  );
    return __find_min_max(0, ENTRIES, 1, data, '1);
  endfunction
endinterface
