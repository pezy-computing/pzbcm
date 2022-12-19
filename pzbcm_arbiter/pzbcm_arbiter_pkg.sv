//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
package pzbcm_arbiter_pkg;
  localparam  int PZBCM_ARBITER_MAX_REQUESTS  =
    `ifdef  PZBCM_ARBITER_MAX_REQUESTS  `PZBCM_ARBITER_MAX_REQUESTS
    `else                               32
    `endif;

  localparam  int PZBCM_ARBIER_MAX_PRIORITY =
    `ifdef  PZBCM_ARBIER_MAX_PRIORITY `PZBCM_ARBIER_MAX_PRIORITY
    `else                             255
    `endif;

  localparam  int PZBCM_ARBITER_MAX_WEIGHT  =
    `ifdef  PZBCM_ARBITER_MAX_WEIGHT  `PZBCM_ARBITER_MAX_WEIGHT
    `else                             255
    `endif;

  localparam  int PZBCM_ARBITER_PRIORITY_WIDTH  = $clog2(PZBCM_ARBIER_MAX_PRIORITY + 1);
  localparam  int PZBCM_ARBITER_WEIGHT_WIDTH    = $clog2(PZBCM_ARBITER_MAX_WEIGHT  + 1);

  typedef enum logic [2:0] {
    PZBCM_ARBITER_FIXED_PRIORITY,
    PZBCM_ARBITER_ROUND_ROBIN,
    PZBCM_ARBITER_INCREMENTAL_ROUND_ROBIN,
    PZBCM_ARBITER_DECREMENTAL_ROUND_ROBIN,
    PZBCM_ARBITER_LRU,
    PZBCM_ARBITER_MRU
  } pzbcm_arbiter_type;

  function automatic int calc_grant_width(int requests, bit onehot_grant);
    if (requests == 1) begin
      return 1;
    end
    else if (onehot_grant) begin
      return requests;
    end
    else begin
      return $clog2(requests);
    end
  endfunction


  typedef logic [PZBCM_ARBITER_MAX_REQUESTS-1:0]                        pzbcm_arbiter_priority_row;
  typedef pzbcm_arbiter_priority_row  [PZBCM_ARBITER_MAX_REQUESTS-1:0]  pzbcm_arbiter_priority_matrix;

  typedef logic [PZBCM_ARBITER_PRIORITY_WIDTH-1:0]                  pzbcm_arbiter_priority;
  typedef pzbcm_arbiter_priority  [PZBCM_ARBITER_MAX_REQUESTS-1:0]  pzbcm_arbiter_priority_list;

  typedef logic [PZBCM_ARBITER_WEIGHT_WIDTH-1:0]                  pzbcm_arbiter_weight;
  typedef pzbcm_arbiter_weight  [PZBCM_ARBITER_MAX_REQUESTS-1:0]  pzbcm_arbiter_weight_list;

  typedef struct packed {
    pzbcm_arbiter_type            arbiter_type;
    logic                         reset;
    pzbcm_arbiter_priority_list   request_priority;
    logic                         weight_valid;
    pzbcm_arbiter_weight_list     weight;
    pzbcm_arbiter_priority_matrix priority_matrix;
  } pzbcm_arbiter_config;

  localparam  pzbcm_arbiter_config  PZBCM_ARBITER_CONFIG_FIXED_PRIORITY = '{
    arbiter_type:     PZBCM_ARBITER_FIXED_PRIORITY,
    reset:            '0,
    request_priority: '0,
    weight_valid:     '0,
    weight:           '0,
    priority_matrix:  '1
  };

  localparam  pzbcm_arbiter_config  PZBCM_ARBITER_CONFIG_ROUND_ROBIN  = '{
    arbiter_type:     PZBCM_ARBITER_ROUND_ROBIN,
    reset:            '0,
    request_priority: '0,
    weight_valid:     '0,
    weight:           '0,
    priority_matrix:  '0
  };

  localparam  pzbcm_arbiter_config  PZBCM_ARBITER_CONFIG_LRU  = '{
    arbiter_type:     PZBCM_ARBITER_LRU,
    reset:            '0,
    request_priority: '0,
    weight_valid:     '0,
    weight:           '0,
    priority_matrix:  '1
  };
endpackage
