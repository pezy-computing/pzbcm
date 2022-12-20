//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_arbiter
  import  pzbcm_arbiter_pkg::*;
#(
  parameter int                           REQUESTS        = 2,
  parameter bit                           ONEHOT_GRANT    = 1,
  parameter bit [1:0]                     ENABLE_ARBITER  = '1,
  parameter int                           PRIORITY_WIDTH  = 0,
  parameter int                           WEIGHT_WIDTH    = 0,
  parameter pzbcm_arbiter_weight_list     WEIGHT          = '1,
  parameter pzbcm_arbiter_priority_matrix PRIORITY_MATRIX = '1,
  parameter bit                           KEEP_RESULT     = 1,
  parameter int                           GRANT_WIDTH     = calc_grant_width(REQUESTS, ONEHOT_GRANT)
)(
  input   var                       i_clk,
  input   var                       i_rst_n,
  input   var pzbcm_arbiter_config  i_config,
  input   var [REQUESTS-1:0]        i_request,
  output  var [GRANT_WIDTH-1:0]     o_grant,
  input   var [REQUESTS-1:0]        i_free
);
  initial begin
    assume (REQUESTS <= PZBCM_ARBITER_MAX_REQUESTS);
    assume (WEIGHT_WIDTH <= PZBCM_ARBITER_WEIGHT_WIDTH);
    assume (ENABLE_ARBITER != '0);
  end

  if (REQUESTS > 1) begin : g
    pzbcm_arbiter_core #(
      .REQUESTS         (REQUESTS         ),
      .ONEHOT_GRANT     (ONEHOT_GRANT     ),
      .ENABLE_ARBITER   (ENABLE_ARBITER   ),
      .PRIORITY_WIDTH   (PRIORITY_WIDTH   ),
      .WEIGHT_WIDTH     (WEIGHT_WIDTH     ),
      .WEIGHT           (WEIGHT           ),
      .PRIORITY_MATRIX  (PRIORITY_MATRIX  ),
      .KEEP_RESULT      (KEEP_RESULT      ),
      .GRANT_WIDTH      (GRANT_WIDTH      )
    ) u_core (
      .i_clk      (i_clk      ),
      .i_rst_n    (i_rst_n    ),
      .i_config   (i_config   ),
      .i_request  (i_request  ),
      .o_grant    (o_grant    ),
      .i_free     (i_free     )
    );
  end
  else begin : g
    always_comb begin
      if (ONEHOT_GRANT) begin
        o_grant = '1;
      end
      else begin
        o_grant = GRANT_WIDTH'(0);
      end
    end
  end
endmodule
