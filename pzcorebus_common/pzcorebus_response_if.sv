//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzcorebus_response_if
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG  = '0
);
  `include  "pzcorebus_if_internal_macros.svh"
  `include  "pzcorebus_macros.svh"

//--------------------------------------------------------------
//  Type Definitions
//--------------------------------------------------------------
  `pzcorebus_if_define_types(BUS_CONFIG)

//--------------------------------------------------------------
//  Signal Declarations
//--------------------------------------------------------------
  `pzcorebus_if_declare_response_signals

//--------------------------------------------------------------
//  API
//--------------------------------------------------------------
  `pzcorebus_if_define_response_api(BUS_CONFIG)

//--------------------------------------------------------------
//  Modport
//--------------------------------------------------------------
  `pzcorebus_if_define_response_modports
endinterface
