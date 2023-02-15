//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_arbiter_core
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
  logic                         busy;
  logic [GRANT_WIDTH-1:0]       grant_round_robin;
  logic [GRANT_WIDTH-1:0]       grant_matrix;
  logic [1:0][GRANT_WIDTH-1:0]  grant;

//--------------------------------------------------------------
//  Arbiters
//--------------------------------------------------------------
  logic select_round_robin;

  always_comb begin
    select_round_robin  = i_config.arbiter_type == PZBCM_ARBITER_ROUND_ROBIN;
  end

  if (ENABLE_ARBITER[0]) begin : g_round_robin_arbiter
    logic enable;

    always_comb begin
      enable  = (!busy) && select_round_robin;
    end

    pzbcm_round_robin_arbiter #(
      .REQUESTS       (REQUESTS       ),
      .PRIORITY_WIDTH (PRIORITY_WIDTH ),
      .WEIGHT_WIDTH   (WEIGHT_WIDTH   ),
      .WEIGHT         (WEIGHT         ),
      .ONEHOT_GRANT   (ONEHOT_GRANT   ),
      .GRANT_WIDTH    (GRANT_WIDTH    )
    ) u_round_robin_arbiter (
      .i_clk      (i_clk              ),
      .i_rst_n    (i_rst_n            ),
      .i_enable   (enable             ),
      .i_config   (i_config           ),
      .i_request  (i_request          ),
      .o_grant    (grant_round_robin  )
    );
  end
  else begin : g_round_robin_arbiter
    always_comb begin
      grant_round_robin = GRANT_WIDTH'(0);
    end
  end

  if (ENABLE_ARBITER[1]) begin : g_matrix_arbiter
    logic enable;

    always_comb begin
      if (ENABLE_ARBITER[0]) begin
        enable  = (!busy) && (!select_round_robin);
      end
      else begin
        enable  = !busy;
      end
    end

    pzbcm_matrix_arbiter #(
      .REQUESTS         (REQUESTS         ),
      .PRIORITY_MATRIX  (PRIORITY_MATRIX  ),
      .ONEHOT_GRANT     (ONEHOT_GRANT     ),
      .GRANT_WIDTH      (GRANT_WIDTH      )
    ) u_matrix_arbiter (
      .i_clk      (i_clk        ),
      .i_rst_n    (i_rst_n      ),
      .i_enable   (enable       ),
      .i_config   (i_config     ),
      .i_request  (i_request    ),
      .o_grant    (grant_matrix )
    );
  end
  else begin : g_matrix_arbiter
    always_comb begin
      grant_matrix  = GRANT_WIDTH'(0);
    end
  end

//--------------------------------------------------------------
//  Grant
//--------------------------------------------------------------
  always_comb begin
    case (i_config.arbiter_type)
      PZBCM_ARBITER_ROUND_ROBIN:  grant[0]  = grant_round_robin;
      default:                    grant[0]  = grant_matrix;
    endcase
  end

  if (KEEP_RESULT) begin : g_result
    logic                   update_grant;
    logic [GRANT_WIDTH-1:0] grant_latched;
    logic                   free;

    always_comb begin
      update_grant  = (i_request != '0) && (!busy);
      grant[1]      = (update_grant) ? grant[0] : grant_latched;
    end

    if (ONEHOT_GRANT) begin : g_free
      always_comb begin
        free  = (i_free & grant[1]) != '0;
      end
    end
    else begin : g_free
      always_comb begin
        free  = i_free[grant[1]];
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        busy  <= '0;
      end
      else if (free) begin
        busy  <= '0;
      end
      else if (update_grant) begin
        busy  <= '1;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        grant_latched <= GRANT_WIDTH'(0);
      end
      else if (update_grant) begin
        grant_latched <= grant[0];
      end
    end
  end
  else begin : g_result
    always_comb begin
      busy      = '0;
      grant[1]  = grant[0];
    end
  end

  always_comb begin
    o_grant = grant[1];
  end
endmodule
