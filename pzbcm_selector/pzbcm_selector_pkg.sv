//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
package pzbcm_selector_pkg;
  typedef enum bit [1:0] {
    PZBCM_SELECTOR_BINARY,
    PZBCM_SELECTOR_PRIORITY,
    PZBCM_SELECTOR_ONEHOT
  } pzbcm_selector_type;

  function automatic int calc_binary_index_width(int entries);
    return (entries > 2) ? $clog2(entries) : 1;
  endfunction

  function automatic int calc_select_width(
    pzbcm_selector_type selector_type,
    int                 entries
  );
    if (selector_type != PZBCM_SELECTOR_BINARY) begin
      return entries;
    end
    else begin
      return calc_binary_index_width(entries);
    end
  endfunction
endpackage
