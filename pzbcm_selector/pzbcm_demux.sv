//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_demux #(
  parameter   int   WIDTH         = 8,
  parameter   type  TYPE          = logic[WIDTH-1:0],
  parameter   int   ENTRIES       = 2,
  parameter   bit   ONE_HOT       = 1,
  parameter   TYPE  DEFAULT       = TYPE'(0),
  localparam  int   SELECT_WIDTH  = (ONE_HOT) ? ENTRIES : $clog2(ENTRIES)
)(
  input   var [SELECT_WIDTH-1:0]  i_select,
  input   var TYPE                i_data,
  output  var TYPE                o_data[ENTRIES]
);
  if (ONE_HOT) begin : g_one_hot
    for (genvar i = 0;i < ENTRIES;++i) begin : g
      assign  o_data[i] = (i_select[i]) ? i_data : DEFAULT;
    end
  end
  else begin : g_binary
    for (genvar i = 0;i < ENTRIES;++i) begin : g
      localparam  bit [SELECT_WIDTH-1:0]  INDEX = i;
      assign  o_data[i] = (i_select == INDEX) ? i_data : DEFAULT;
    end
  end
endmodule
