//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
`define pzhsbus_check(item, expected) \
  `ifndef SYNTHESIS \
    initial begin \
      assume ( $typename(item.payload) == $typename(expected) ) \
      else $error("The type of 'item' in '%m' doesn't match 'expected'."); \
    end \
  `endif
