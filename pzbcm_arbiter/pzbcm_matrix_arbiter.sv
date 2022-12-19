//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzbcm_matrix_arbiter
  import  pzbcm_arbiter_pkg::*;
#(
  parameter int                           REQUESTS        = 2,
  parameter pzbcm_arbiter_priority_matrix PRIORITY_MATRIX = '1,
  parameter bit                           ONEHOT_GRANT    = 1,
  parameter int                           GRANT_WIDTH     = calc_grant_width(REQUESTS, ONEHOT_GRANT)
)(
  input   var                       i_clk,
  input   var                       i_rst_n,
  input   var                       i_enable,
  input   var pzbcm_arbiter_config  i_config,
  input   var [REQUESTS-1:0]        i_request,
  output  var [GRANT_WIDTH-1:0]     o_grant
);
  logic [REQUESTS-1:0]                request;
  logic [REQUESTS-1:0]                grant;
  logic [REQUESTS-1:0][REQUESTS-1:0]  priority_matrix;
  logic [REQUESTS-1:0][REQUESTS-1:0]  priority_matrix_next;

//--------------------------------------------------------------
//  Grant generation
//--------------------------------------------------------------
  if (ONEHOT_GRANT) begin : g_onehot_grant
    always_comb begin
      o_grant = grant;
    end
  end
  else begin : g_binary_grant
    pzbcm_onehot #(REQUESTS)  u_onehot();
    always_comb begin
      o_grant = u_onehot.to_binary(grant);
    end
  end

  always_comb begin
    request = (i_enable) ? i_request : '0;
    grant   = compute_grant(request, priority_matrix);
  end

  function automatic logic [REQUESTS-1:0] compute_grant(
    logic [REQUESTS-1:0]                request,
    logic [REQUESTS-1:0][REQUESTS-1:0]  priority_matrix
  );
    logic [REQUESTS-1:0]  grant;

    for (int columun = 0;columun < REQUESTS;++columun) begin
      logic [REQUESTS-1:0]  columun_vector;

      for (int row = 0;row < REQUESTS;++row) begin
        columun_vector[row] = (row != columun) && request[row] && priority_matrix[row][columun];
      end

      grant[columun]  = request[columun] && (columun_vector == '0);
    end

    return grant;
  endfunction

//--------------------------------------------------------------
//  Priority matrix
//--------------------------------------------------------------
  always_comb begin
    priority_matrix_next  = update_priority_matrix(i_config, priority_matrix, grant);
  end

  for (genvar row = 0;row < REQUESTS;++row) begin : g_row
    for (genvar columun = 0;columun < REQUESTS;++columun) begin : g_column
      if (columun < row) begin : g
        always_comb begin
          priority_matrix[row][columun] = ~priority_matrix[columun][row];
        end
      end
      else if (columun == row) begin : g
        always_comb begin
          priority_matrix[row][columun] = '0;
        end
      end
      else begin : g
        logic priority_value;

        always_ff @(posedge i_clk, negedge i_rst_n) begin
          if (!i_rst_n) begin
            priority_value  <= PRIORITY_MATRIX[row][columun];
          end
          else if (i_config.reset) begin
            priority_value  <= i_config.priority_matrix[row][columun];
          end
          else if (request != '0) begin
            priority_value  <= priority_matrix_next[row][columun];
          end
        end

        always_comb begin
          priority_matrix[row][columun] = priority_value;
        end
      end
    end
  end

  function automatic logic [REQUESTS-1:0][REQUESTS-1:0] update_priority_matrix(
    pzbcm_arbiter_config                arbiter_config,
    logic [REQUESTS-1:0][REQUESTS-1:0]  priority_matrix,
    logic [REQUESTS-1:0]                grant
  );
    logic [REQUESTS-1:0]                update_position;
    logic                               row_value;
    logic                               columun_value;
    logic [REQUESTS-1:0][REQUESTS-1:0]  matrix_next;

    case (arbiter_config.arbiter_type)
      PZBCM_ARBITER_ROUND_ROBIN,
      PZBCM_ARBITER_INCREMENTAL_ROUND_ROBIN: begin
        for (int row = 0;row < REQUESTS;++row) begin
          update_position[row]  = is_highest_priority(row, priority_matrix[row]);
        end
        row_value     = '0;
        columun_value = '1;
      end
      PZBCM_ARBITER_DECREMENTAL_ROUND_ROBIN: begin
        for (int row = 0;row < REQUESTS;++row) begin
          update_position[row]  = is_lowest_priority(priority_matrix[row]);
        end
        row_value     = '1;
        columun_value = '0;
      end
      PZBCM_ARBITER_LRU: begin
        update_position = grant;
        row_value       = '0;
        columun_value   = '1;
      end
      PZBCM_ARBITER_MRU: begin
        update_position = grant;
        row_value       = '1;
        columun_value   = '0;
      end
      default: begin
        update_position = '0;
        row_value       = '0;
        columun_value   = '0;
      end
    endcase

    matrix_next = priority_matrix;
    for (int row = 0;row < REQUESTS;++row) begin
      for (int columun = row + 1;columun < REQUESTS;++columun) begin
        if (update_position[columun]) begin
          matrix_next[row][columun] = columun_value;
        end
        else if (update_position[row]) begin
          matrix_next[row][columun] = row_value;
        end
      end
    end

    return matrix_next;
  endfunction

  function automatic logic is_highest_priority(int row_index, logic [REQUESTS-1:0] row_vector);
    logic [REQUESTS-1:0]  vector;
    vector            = row_vector;
    vector[row_index] = '1;
    return vector == '1;
  endfunction

  function automatic logic is_lowest_priority(logic [REQUESTS-1:0] row_vector);
    return row_vector == '0;
  endfunction

`ifndef SYNTHESIS
  bit [REQUESTS-1:0][$clog2(REQUESTS)-1:0]  priority_values;

  always_comb begin
    for (int i = 0;i < REQUESTS;++i) begin
      priority_values[i]  = $countones(priority_matrix[i]);
    end
  end

  `ifdef PZBCM_ARBITER_ENABLE_SVA
  tb_pzbcm_matrix_arbiter_sva #(REQUESTS) u_sva (
    .i_clk              (i_clk            ),
    .i_rst_n            (i_rst_n          ),
    .i_busy             (busy             ),
    .i_request          (i_request        ),
    .i_grant            (grant[1]         ),
    .i_priority_matrix  (priority_matrix  )
  );
  `endif
`endif
endmodule
