//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
interface pzcorebus_request_if
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
  `pzcorebus_if_declare_request_signals

//--------------------------------------------------------------
//  API
//--------------------------------------------------------------
  `pzcorebus_if_define_request_api(BUS_CONFIG)

//--------------------------------------------------------------
//  Modport
//--------------------------------------------------------------
  `pzcorebus_if_define_request_modports
endinterface
