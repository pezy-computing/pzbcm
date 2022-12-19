//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
package pzbcm_async_fifo_pkg;
  function automatic int calc_default_depth(int stages);
    return 2**($clog2(3 * stages) + 1);
  endfunction
endpackage
