//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
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
    logic                         busy;
    logic [1:0]                   select_arbiter;
    logic [1:0]                   enable_arbiter;
    logic [1:0][GRANT_WIDTH-1:0]  grant_raw;
    logic [1:0][GRANT_WIDTH-1:0]  grant;
    logic                         select_rr;

    always_comb begin
      case (i_config.arbiter_type)
        PZBCM_ARBITER_ROUND_ROBIN,
        PZBCM_ARBITER_FIXED_PRIORITY: begin
          select_arbiter[0] = ENABLE_ARBITER[0];
          select_arbiter[1] = '0;
        end
        default: begin
          select_arbiter[0] = '0;
          select_arbiter[1] = ENABLE_ARBITER[1];
        end
      endcase

      enable_arbiter[0] = select_arbiter[0] && (!busy);
      enable_arbiter[1] = select_arbiter[1] && (!busy);
    end

    //----------------------
    //  Arbiter
    //----------------------
    if (ENABLE_ARBITER[0]) begin : g_round_robin
      pzbcm_round_robin_arbiter #(
        .REQUESTS       (REQUESTS       ),
        .PRIORITY_WIDTH (PRIORITY_WIDTH ),
        .WEIGHT_WIDTH   (WEIGHT_WIDTH   ),
        .WEIGHT         (WEIGHT         ),
        .ONEHOT_GRANT   (ONEHOT_GRANT   ),
        .GRANT_WIDTH    (GRANT_WIDTH    )
      ) u_arbiter (
        .i_clk      (i_clk              ),
        .i_rst_n    (i_rst_n            ),
        .i_enable   (enable_arbiter[0]  ),
        .i_config   (i_config           ),
        .i_request  (i_request          ),
        .o_grant    (grant_raw[0]       )
      );
    end
    else begin : g_round_robin
      always_comb begin
        grant_raw[0]  = GRANT_WIDTH'(0);
      end
    end

    if (ENABLE_ARBITER[1]) begin : g_matrix
      pzbcm_matrix_arbiter #(
        .REQUESTS         (REQUESTS         ),
        .PRIORITY_MATRIX  (PRIORITY_MATRIX  ),
        .ONEHOT_GRANT     (ONEHOT_GRANT     ),
        .GRANT_WIDTH      (GRANT_WIDTH      )
      ) u_matrix_arbiter (
        .i_clk      (i_clk              ),
        .i_rst_n    (i_rst_n            ),
        .i_enable   (enable_arbiter[1]  ),
        .i_config   (i_config           ),
        .i_request  (i_request          ),
        .o_grant    (grant_raw[1]       )
      );
    end
    else begin : g_matrix
      always_comb begin
        grant_raw[1]  = GRANT_WIDTH'(0);
      end
    end

    //----------------------
    //  Grant
    //----------------------
    always_comb begin
      grant[0]  = (select_arbiter[0]) ? grant_raw[0] : grant_raw[1];
    end

    if (KEEP_RESULT) begin : g_grant
      logic                   update;
      logic [GRANT_WIDTH-1:0] grant_latched;
      logic                   free;

      always_comb begin
        update    = (i_request != '0) && (!busy);
        grant[1]  = (update) ? grant[0] : grant_latched;
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
        else if (update) begin
          busy  <= '1;
        end
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          grant_latched <= GRANT_WIDTH'(0);
        end
        else if (update) begin
          grant_latched <= grant[0];
        end
      end
    end
    else begin : g_grant
      always_comb begin
        busy      = '0;
        grant[1]  = grant[0];
      end
    end

    always_comb begin
      o_grant = grant[1];
    end
  end
  else if (ONEHOT_GRANT) begin : g
    always_comb begin
      o_grant = '1;
    end
  end
  else begin : g
    always_comb begin
      o_grant = GRANT_WIDTH'(0);
    end
  end
endmodule
