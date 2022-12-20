//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_mux #(
  parameter   int   WIDTH         = 8,
  parameter   type  TYPE          = logic[WIDTH-1:0],
  parameter   int   ENTRIES       = 2,
  parameter   bit   ONE_HOT       = 1,
  localparam  int   INDEX_WIDTH   = $clog2(ENTRIES),
  localparam  int   SELECT_WIDTH  = (ONE_HOT) ? ENTRIES : INDEX_WIDTH
)(
  input   var [SELECT_WIDTH-1:0]  i_select,
  input   var TYPE                i_data[ENTRIES],
  output  var TYPE                o_data
);
  TYPE  [ENTRIES-1:0] data;

  pzbcm_selector #(
    .WIDTH    (WIDTH    ),
    .TYPE     (TYPE     ),
    .ENTRIES  (ENTRIES  )
  ) u_selector ();

  always_comb begin
    for (int i = 0;i < ENTRIES;++i) begin
      data[i] = i_data[i];
    end

    if (ONE_HOT) begin
      o_data  = u_selector.onehot_mux(ENTRIES'(i_select), data);
    end
    else begin
      o_data  = u_selector.binary_mux(INDEX_WIDTH'(i_select), data);
    end
  end
endmodule
