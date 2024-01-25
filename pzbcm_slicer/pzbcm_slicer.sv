//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_slicer #(
  parameter int   WIDTH           = 1,
  parameter type  TYPE            = logic [WIDTH-1:0],
  parameter int   STAGES          = 1,
  parameter bit   ASCENDING_ORDER = 1,
  parameter bit   FULL_BANDWIDTH  = 1,
  parameter bit   DISABLE_MBFF    = 0,
  parameter bit   USE_RESET       = 1
)(
  input   var       i_clk,
  input   var       i_rst_n,
  input   var       i_valid,
  output  var       o_ready,
  input   var TYPE  i_data,
  output  var       o_valid,
  input   var       i_ready,
  output  var TYPE  o_data
);
  localparam  int W = $bits(TYPE);

  logic [STAGES+1-1:0]        valid;
  logic [STAGES+1-1:0]        ready;
  logic [STAGES+1-1:0][W-1:0] data;

  if (ASCENDING_ORDER) begin : g_ascending_order
    always_comb begin
      o_ready   = ready[0];
      valid[0]  = i_valid;
      data[0]   = i_data;
    end

    always_comb begin
      ready[STAGES] = i_ready;
      o_valid       = valid[STAGES];
      o_data        = TYPE'(data[STAGES]);
    end

    for (genvar i = 0;i < STAGES;++i) begin : g
      pzbcm_slicer_unit #(
        .WIDTH          (W              ),
        .FULL_BANDWIDTH (FULL_BANDWIDTH ),
        .DISABLE_MBFF   (DISABLE_MBFF   ),
        .USE_RESET      (USE_RESET      )
      ) u_slicer_unit (
        .i_clk    (i_clk      ),
        .i_rst_n  (i_rst_n    ),
        .i_valid  (valid[i+0] ),
        .o_ready  (ready[i+0] ),
        .i_data   (data[i+0]  ),
        .o_valid  (valid[i+1] ),
        .i_ready  (ready[i+1] ),
        .o_data   (data[i+1]  )
      );
    end
  end
  else begin : g_descending_order
    always_comb begin
      o_ready       = ready[STAGES];
      valid[STAGES] = i_valid;
      data[STAGES]  = i_data;
    end

    always_comb begin
      ready[0]  = i_ready;
      o_valid   = valid[0];
      o_data    = TYPE'(data[0]);
    end

    for (genvar i = STAGES;i > 0;--i) begin : g
      pzbcm_slicer_unit #(
        .WIDTH          (W              ),
        .FULL_BANDWIDTH (FULL_BANDWIDTH ),
        .DISABLE_MBFF   (DISABLE_MBFF   ),
        .USE_RESET      (USE_RESET      )
      ) u_slicer_unit (
        .i_clk    (i_clk      ),
        .i_rst_n  (i_rst_n    ),
        .i_valid  (valid[i-0] ),
        .o_ready  (ready[i-0] ),
        .i_data   (data[i-0]  ),
        .o_valid  (valid[i-1] ),
        .i_ready  (ready[i-1] ),
        .o_data   (data[i-1]  )
      );
    end
  end
endmodule
