//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_round_robin_arbiter
  import  pzbcm_arbiter_pkg::*;
#(
  parameter int                       REQUESTS        = 2,
  parameter int                       PRIORITY_WIDTH  = 0,
  parameter int                       WEIGHT_WIDTH    = 0,
  parameter pzbcm_arbiter_weight_list WEIGHT          = '1,
  parameter bit                       ONEHOT_GRANT    = 1,
  parameter int                       GRANT_WIDTH     = calc_grant_width(REQUESTS, ONEHOT_GRANT)
)(
  input   var                       i_clk,
  input   var                       i_rst_n,
  input   var                       i_enable,
  input   var pzbcm_arbiter_config  i_config,
  input   var [REQUESTS-1:0]        i_request,
  output  var [GRANT_WIDTH-1:0]     o_grant
);
  function automatic int get_compare_value_width();
    int width = 0;
    width += 1;
    width += ((WEIGHT_WIDTH > 0) ? 1 : 0);
    width += ((PRIORITY_WIDTH > 0) ? PRIORITY_WIDTH : 0);
    width += 1;
    return width;
  endfunction

  localparam  int COMPARE_WIDTH         = get_compare_value_width();
  localparam  int ACTUAL_PRIORITY_WIDTH = (PRIORITY_WIDTH > 0) ? PRIORITY_WIDTH : 1;
  localparam  int ACTUAL_WEIGHT_WIDTH   = (WEIGHT_WIDTH   > 0) ? WEIGHT_WIDTH   : 1;
  localparam  int INDEX_WIDTH           = $clog2(REQUESTS);

  typedef struct packed {
    logic [INDEX_WIDTH-1:0]   index;
    logic [COMPARE_WIDTH-1:0] compare_value;
  } pzbcm_compare_data;

  typedef struct packed {
    logic [REQUESTS-1:0]  location;
    pzbcm_compare_data    data;
  } pzbcm_compare_result;

  logic [REQUESTS-1:0]                          request;
  logic [INDEX_WIDTH-1:0]                       current_grant;
  logic [REQUESTS-1:0][ACTUAL_WEIGHT_WIDTH-1:0] weight;
  pzbcm_compare_data  [REQUESTS-1:0]            compare_data;
  pzbcm_compare_result                          compare_result;
  logic                                         use_round_robin;

  pzbcm_min_max_finder #(
    .ENTRIES        (REQUESTS             ),
    .TYPE           (pzbcm_compare_data   ),
    .RESULT         (pzbcm_compare_result ),
    .COMPARE_WIDTH  (COMPARE_WIDTH        )
  ) u_max_finder();

  localparam  int WEIGHT_LSB    = 1;
  localparam  int PRIORITY_LSB  = WEIGHT_LSB   + WEIGHT_WIDTH;
  localparam  int REQUEST_LSB   = PRIORITY_LSB + PRIORITY_WIDTH;

  function automatic pzbcm_compare_data [REQUESTS-1:0] get_compare_data(
    logic [INDEX_WIDTH-1:0]                       current_grant,
    logic [REQUESTS-1:0]                          request,
    pzbcm_arbiter_config                          arbiter_config,
    logic                                         use_round_robin,
    logic [REQUESTS-1:0][ACTUAL_WEIGHT_WIDTH-1:0] weight
  );
    pzbcm_compare_data [REQUESTS-1:0] data;
    logic [COMPARE_WIDTH-1:0]         value;

    for (int i = 0;i < REQUESTS;++i) begin
      value[0]            = use_round_robin && (INDEX_WIDTH'(i) > current_grant);
      value[REQUEST_LSB]  = request[i];
      if (WEIGHT_WIDTH > 0) begin
        value[WEIGHT_LSB] = weight[i] > ACTUAL_WEIGHT_WIDTH'(0);
      end
      if (PRIORITY_WIDTH > 0) begin
        value[PRIORITY_LSB+:ACTUAL_PRIORITY_WIDTH]  = ACTUAL_PRIORITY_WIDTH'(arbiter_config.request_priority[i]);
      end

      data[i].index         = INDEX_WIDTH'(i);
      data[i].compare_value = value;
    end

    return data;
  endfunction

  always_comb begin
    use_round_robin = i_config.arbiter_type == PZBCM_ARBITER_ROUND_ROBIN;
  end

  always_comb begin
    request         = (i_enable) ? i_request : '0;
    compare_data    = get_compare_data(current_grant, request, i_config, use_round_robin, weight);
    compare_result  = u_max_finder.find_max(compare_data);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      current_grant <= INDEX_WIDTH'(0);
    end
    else if (i_config.reset || (!use_round_robin)) begin
      current_grant <= INDEX_WIDTH'(0);
    end
    else if (request != '0) begin
      current_grant <= compare_result.data.index;
    end
  end

  if (ONEHOT_GRANT) begin : g
    always_comb begin
      o_grant = compare_result.location;
    end
  end
  else begin : g
    always_comb begin
      o_grant = compare_result.data.index;
    end
  end

  if (WEIGHT_WIDTH > 0) begin : g_weight
    localparam  int                         RESET_COUNT_WIDTH = $clog2(REQUESTS);
    localparam  bit [RESET_COUNT_WIDTH-1:0] MAX_RESET_COUNT   = RESET_COUNT_WIDTH'(REQUESTS - 1);

    logic [REQUESTS-1:0]          weight_eq_0;
    logic [REQUESTS-1:0]          weight_0_grant;
    logic [RESET_COUNT_WIDTH-1:0] reset_count;
    logic [2:0]                   reset_weight;

    always_comb begin
      reset_weight[0] = i_config.reset || (!use_round_robin);
      reset_weight[1] = (weight_0_grant != '0) && (reset_count == MAX_RESET_COUNT);
      reset_weight[2] = weight_eq_0 == '1;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        reset_count <= RESET_COUNT_WIDTH'(0);
      end
      else if (reset_weight != '0) begin
        reset_count <= RESET_COUNT_WIDTH'(0);
      end
      else if (weight_0_grant != '0) begin
        reset_count <= reset_count + RESET_COUNT_WIDTH'(1);
      end
    end

    for (genvar i = 0;i < REQUESTS;++i) begin : g
      logic grant;
      logic eq_0;
      logic eq_1;

      always_comb begin
        grant             = request[i] && compare_result.location[i];
        eq_0              = weight[i] == WEIGHT_WIDTH'(0);
        eq_1              = weight[i] == WEIGHT_WIDTH'(1);
        weight_eq_0[i]    = (grant && eq_1) || eq_0;
        weight_0_grant[i] = grant && eq_0;
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          weight[i] <= WEIGHT_WIDTH'(WEIGHT[i]);
        end
        else if (reset_weight != '0) begin
          if (i_config.weight_valid) begin
            weight[i] <= WEIGHT_WIDTH'(i_config.weight[i]);
          end
          else begin
            weight[i] <= WEIGHT_WIDTH'(WEIGHT[i]);
          end
        end
        else if (grant && (!eq_0)) begin
          weight[i] <= weight[i] - WEIGHT_WIDTH'(1);
        end
      end
    end
  end
  else begin : g_weight
    always_comb begin
      weight  = '0;
    end
  end
endmodule
