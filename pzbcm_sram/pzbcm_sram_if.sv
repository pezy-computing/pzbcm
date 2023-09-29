//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzbcm_sram_if #(
  parameter int   WORDS         = 2,
  parameter int   DATA_WIDTH    = 8,
  parameter type  READ_INFO     = logic,
  parameter int   POINTER_WIDTH = (WORDS > 0) ? $clog2(WORDS) : 1
);
  typedef struct packed {
    READ_INFO               info;
    logic [DATA_WIDTH-1:0]  data;
  } pzbcm_sram_read_data;

  logic                     write_ready;
  logic                     write_valid;
  logic [POINTER_WIDTH-1:0] write_pointer;
  logic [DATA_WIDTH-1:0]    write_data;
  logic                     read_ready;
  logic                     read_valid;
  logic [POINTER_WIDTH-1:0] read_pointer;
  READ_INFO                 read_info;
  logic                     read_data_ready;
  logic                     read_data_valid;
  pzbcm_sram_read_data      read_data;
  logic                     read_busy;
  logic                     fifo_empty;
  logic                     fifo_almost_full;
  logic                     fifo_full;

  function automatic logic write_ack();
    return write_ready && write_valid;
  endfunction

  function automatic logic read_ack();
    return read_ready && read_valid;
  endfunction

  function automatic logic read_data_ack();
    return read_data_ready && read_data_valid;
  endfunction

  modport write_port (
    input   write_ready,
    output  write_valid,
    output  write_pointer,
    output  write_data,
    import  write_ack
  );

  modport read_port (
    input   read_ready,
    output  read_valid,
    output  read_pointer,
    output  read_info,
    output  read_data_ready,
    input   read_data_valid,
    input   read_data,
    import  read_ack,
    import  read_data_ack
  );

  modport sram (
    output  write_ready,
    input   write_valid,
    input   write_pointer,
    input   write_data,
    output  read_ready,
    input   read_valid,
    input   read_pointer,
    input   read_info,
    input   read_data_ready,
    output  read_data_valid,
    output  read_data,
    output  read_busy,
    output  fifo_empty,
    output  fifo_almost_full,
    output  fifo_full,
    import  write_ack,
    import  read_ack,
    import  read_data_ack
  );

  modport monitor (
    input   write_ready,
    input   write_valid,
    input   write_pointer,
    input   write_data,
    input   read_ready,
    input   read_valid,
    input   read_pointer,
    input   read_info,
    input   read_data_ready,
    input   read_data_valid,
    input   read_data,
    input   read_busy,
    input   fifo_empty,
    input   fifo_almost_full,
    input   fifo_full,
    import  write_ack,
    import  read_ack,
    import  read_data_ack
  );
endinterface
