//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_ff_slicer #(
  parameter int   WIDTH           = 1,
  parameter type  TYPE            = logic [WIDTH-1:0],
  parameter int   STAGES          = 1,
  parameter bit   ASCENDING_ORDER = 1,
  parameter bit   DISABLE_MBFF    = 0
)(
  input   var       i_clk,
  input   var       i_rst_n,
  input   var TYPE  i_d,
  output  var TYPE  o_q
);
  logic [STAGES:0][$bits(TYPE)-1:0] q;

  if (ASCENDING_ORDER) begin : g
    always_comb begin
      q[0]  = i_d;
    end

    always_comb begin
      o_q = TYPE'(q[STAGES]);
    end

    for (genvar i = 0;i < STAGES;++i) begin : g
      pzbcm_ff_slicer_unit #(
        .WIDTH        ($bits(TYPE)  ),
        .DISABLE_MBFF (DISABLE_MBFF )
      ) u_slicer (
        .i_clk    (i_clk    ),
        .i_rst_n  (i_rst_n  ),
        .i_d      (q[i+0]   ),
        .o_q      (q[i+1]   )
      );
    end
  end
  else begin : g
    always_comb begin
      q[STAGES] = i_d;
    end

    always_comb begin
      o_q = TYPE'(q[0]);
    end

    for (genvar i = 0;i < STAGES;++i) begin : g
      pzbcm_ff_slicer_unit #(
        .WIDTH        ($bits(TYPE)  ),
        .DISABLE_MBFF (DISABLE_MBFF )
      ) u_slicer (
        .i_clk    (i_clk    ),
        .i_rst_n  (i_rst_n  ),
        .i_d      (q[i+1]   ),
        .o_q      (q[i+0]   )
      );
    end
  end
endmodule

module pzbcm_ff_slicer_unit #(
  parameter int WIDTH         = 1,
  parameter bit DISABLE_MBFF  = 0
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var [WIDTH-1:0] i_d,
  output  var [WIDTH-1:0] o_q
);
  if (!DISABLE_MBFF) begin : g
    logic [WIDTH-1:0] q;

    always_comb begin
      o_q = q;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        q <= '0;
      end
      else begin
        q <= i_d;
      end
    end
  end
  else begin : g
    for (genvar i = 0;i < WIDTH;++i) begin : g
      logic q;

      always_comb begin
        o_q[i]  = q;
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          q <= '0;
        end
        else begin
          q <= i_d[i];
        end
      end
    end
  end
endmodule
