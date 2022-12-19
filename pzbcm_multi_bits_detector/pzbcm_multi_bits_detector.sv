//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzbcm_multi_bits_detector #(
  parameter int N = 2
)(
  input   var [N-1:0] i_bits,
  output  var         o_detect
);
  pzbcm_multi_bits_checker #(N) u_checker();
  always_comb begin
    o_detect  = u_checker.is_multi_bits(i_bits);
  end
endmodule
