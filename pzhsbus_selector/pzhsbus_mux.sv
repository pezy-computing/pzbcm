//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzhsbus_mux #(
  parameter   int SLAVES        = 2,
  parameter   bit ONE_HOT       = 1,
  localparam  int SELECT_WIDTH  = (ONE_HOT) ? SLAVES : $clog2(SLAVES)
)(
  input var [SELECT_WIDTH-1:0]  i_select,
  pzhsbus_if.slave              slave_if[SLAVES],
  pahsbus_if.master             master_if
);
  typedef master_if.__payload __payload;

  logic     valid[SLAVES];
  logic     ready[SLAVES];
  __payload payload[SLAVES];

  for (genvar i = 0;i < SLAVES;++i) begin : g
    assign  valid[i]          = slave_if[i].valid;
    assign  slave_if[i].ready = ready[i];
    assign  payload[i]        = slave_if[i].payload;
  end

  pzbcm_mux #(
    .TYPE     (logic    ),
    .ENTRIES  (SLAVES   ),
    .ONE_HOT  (ONE_HOT  )
  ) u_valid_mux (
    i_select, valid, master_if.valid
  );

  pzbcm_demux #(
    .TYPE     (logic    ),
    .ENTRIES  (SLAVES   ),
    .ONE_HOT  (ONE_HOT  )
  ) u_ready_demux (
    i_select, master_if.ready, ready
  );

  pzbcm_mux #(
    .TYPE     (__payload  ),
    .ENTRIES  (SLAVES     ),
    .ONE_HOT  (ONE_HOT    )
  ) u_payload_mux (
    i_select, payload, master_if.payload
  );
endmodule
