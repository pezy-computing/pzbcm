//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
`ifndef INCLUDED_PZHSBUS_MACROS_SVH
`define INCLUDED_PZHSBUS_MACROS_SVH

`define pzhsbus_renamer(SLAVE, MASTER) \
assign  MASTER.valid    = SLAVE.valid; \
assign  SLAVE.ready     = MASTER.ready; \
assign  MASTER.payload  = SLAVE.payload;

`define pzhsbus_array_if_renamer(SLAVE, MASTER, START_INDEX, SIZE) \
for (genvar i__ = 0;i__ < SIZE;++i__) begin \
  `pzhsbus_renamer(SLAVE[START_INDEX+i__], MASTER[START_INDEX+i__]) \
end

`define pzhsbus_ack(IF) (IF.valid && IF.ready)

`endif
