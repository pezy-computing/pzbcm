//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
interface pzhsbus_if #(
  parameter type  PAYLOAD = logic
);
  typedef PAYLOAD __payload;

  logic   valid;
  logic   ready;
  PAYLOAD payload;

  function automatic logic ack();
    return valid && ready;
  endfunction

  function automatic logic get_ack();
    return ack();
  endfunction

  modport master (
    output  valid,
    input   ready,
    output  payload,
    import  ack,
    import  get_ack
  );

  modport slave (
    input   valid,
    output  ready,
    input   payload,
    import  ack,
    import  get_ack
  );

  modport monitor (
    input   valid,
    input   ready,
    input   payload,
    import  ack,
    import  get_ack
  );
endinterface
