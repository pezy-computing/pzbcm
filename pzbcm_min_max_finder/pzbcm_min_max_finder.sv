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
  localparam  int DEPTH = $clog2(ENTRIES);

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
    TYPE  [ENTRIES-1:0] data
  );
    int                 step;
    int                 current_n;
    int                 next_n;
    logic [ENTRIES-1:0] current_location;
    logic [ENTRIES-1:0] next_location;
    TYPE                current_data[ENTRIES];
    TYPE                next_data[ENTRIES];
    RESULT              result;

    for (int i = 0;i < DEPTH;++i) begin
      if (i == 0) begin
        current_n         = ENTRIES;
        current_location  = '1;
        for (int j = 0;j < ENTRIES;++j) begin
          current_data[j] = data[j];
        end
      end
      else begin
        current_n         = next_n;
        current_location  = next_location;
        current_data      = next_data;
      end

      next_n  = (current_n / 2) + (current_n % 2);
      step    = 2**i;
      for (int j = 0;j < next_n;++j) begin
        logic [1:0] compare_result;

        if (((j + 1) == next_n) && ((current_n % 2) == 1)) begin
          compare_result  = 2'b01;
        end
        else begin
          compare_result  = __do_compare(compare_min, current_data[2*j+0], current_data[2*j+1]);
        end

        if (compare_result[0]) begin
          next_data[j]  = current_data[2*j+0];
        end
        else begin
          next_data[j]  = current_data[2*j+1];
        end

        for (int k = 0;k < (2 * step);++k) begin
          int index = 2 * step * j + k;
          if (index < ENTRIES) begin
            next_location[index]  = compare_result[k/step] && current_location[index];
          end
        end
      end
    end

    result.data     = next_data[0];
    result.location = next_location;
    return result;
  endfunction

  function automatic RESULT find_min(
    TYPE  [ENTRIES-1:0] data
  );
    return __find_min_max(1, data);
  endfunction

  function automatic RESULT find_max(
    TYPE  [ENTRIES-1:0] data
  );
    return __find_min_max(0, data);
  endfunction
endinterface
