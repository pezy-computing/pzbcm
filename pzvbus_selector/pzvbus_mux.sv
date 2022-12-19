//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzvbus_mux #(
  parameter   int SLAVES        = 2,
  parameter   bit ONE_HOT       = 1,
  localparam  int SELECT_WIDTH  = (ONE_HOT) ? SLAVES : $clog2(SLAVES)
)(
  input var [SELECT_WIDTH-1:0]  i_select,
  pzvbus_if.slave               slave_if[SLAVES],
  pzvbus_if.master              master_if
);
  typedef master_if.__payload_with_valid  __payload_with_valid;

  __payload_with_valid  in[SLAVES];
  __payload_with_valid  out;

  for (genvar i = 0;i < SLAVES;++i) begin : g
    assign  in[i].valid = slave_if[i].valid;
    assign  in[i].payload = slave_if[i].payload;
  end

  assign  master_if.valid   = out.valid;
  assign  master_if.payload = out.payload;

  pzbcm_mux #(
    .TYPE     (__payload_with_valid ),
    .ENTRIES  (SLAVES               ),
    .ONE_HOT  (ONE_HOT              )
  ) u_valid_mux (
    i_select, in, out
  );
endmodule
