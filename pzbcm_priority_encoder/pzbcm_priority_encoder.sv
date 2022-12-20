//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzbcm_priority_encoder #(
  parameter int WIDTH = 2
);
  localparam  int OUT_WIDTH = (WIDTH > 1) ? $clog2(WIDTH) : 1;

  pzbcm_selector #(
    .WIDTH    (OUT_WIDTH  ),
    .ENTRIES  (WIDTH      ),
    .BINARY   (0          ),
    .PRIORITY (1          )
  ) u_mux();

  function automatic logic [$clog2(WIDTH)-1:0] encode(
    logic [WIDTH-1:0] in
  );
    logic [WIDTH-1:0][OUT_WIDTH-1:0]  index_value;

    for (int i = 0;i < WIDTH;++i) begin
      index_value[i]  = (OUT_WIDTH)'(i);
    end

    return u_mux.priority_mux(in, index_value);
  endfunction
endinterface
