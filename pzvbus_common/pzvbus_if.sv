
//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
interface pzvbus_if #(
  parameter type  PAYLOAD = logic
);
  typedef PAYLOAD __payload;
  typedef struct packed {
    logic   valid;
    PAYLOAD payload;
  } __payload_with_valid;

  logic   valid;
  PAYLOAD payload;

  modport master (
    output  valid,
    output  payload
  );

  modport slave (
    input valid,
    input payload
  );

  modport monitor (
    input valid,
    input payload
  );
endinterface
