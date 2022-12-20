//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
`ifndef PZBCM_SYNCHRONIZER_DEFAULT_STAGES
  `define PZBCM_SYNCHRONIZER_DEFAULT_STAGES 2
`endif

module pzbcm_synchronizer #(
  parameter int             WIDTH                     = 1,
  parameter int             STAGES                    = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES,
  parameter bit [WIDTH-1:0] INITIAL_VALUE             = '0,
  parameter bit             USE_CUSTOM_IMPLEMENTATION = 1
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var [WIDTH-1:0] i_d,
  output  var [WIDTH-1:0] o_d
);
  localparam  bit NO_CUSTOM_IMPLEMENTATION  = `ifndef PZBCM_SYNCHRONIZER_CUSTOM_IMPLEMENTATION  1
                                              `else                                             0
                                              `endif;

  for (genvar i = 0;i < WIDTH;++i) begin : g
    logic [STAGES-1:0]  d;
    assign  o_d[i]  = d[STAGES-1];

    if (NO_CUSTOM_IMPLEMENTATION || (!USE_CUSTOM_IMPLEMENTATION)) begin : g
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          d <= {STAGES{INITIAL_VALUE[i]}};
        end
        else begin
          d <= {d[STAGES-2:0], i_d[i]};
        end
      end
    end
    else begin : g
`ifdef PZBCM_SYNCHRONIZER_CUSTOM_IMPLEMENTATION
      `include  "pzbcm_synchronizer_custom_implementation.svh"
`endif
    end
  end
endmodule
