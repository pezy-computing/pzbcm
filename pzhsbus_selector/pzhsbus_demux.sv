//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzhsbus_demux #(
  parameter   int MASTERS       = 2,
  parameter   bit ONE_HOT       = 1,
  localparam  int SELECT_WIDTH  = (ONE_HOT) ? MASTERS : $clog2(MASTERS)
)(
  input var [SELECT_WIDTH-1:0]  i_select,
  pzhsbus_if.slave              slave_if,
  pzhsbus_if.master             master_if[MASTERS]
);
  logic valid[MASTERS];
  logic ready[MASTERS];

  for (genvar i = 0;i < MASTERS;++i) begin : g
    assign  master_if[i].valid    = valid;
    assign  ready[i]              = master_if[i].ready;
    assign  master_if[i].payload  = slave_if[i].payload;
  end

  pzbcm_demux #(
    .TYPE     (logic    ),
    .ENTRIES  (MASTERS  ),
    .ONE_HOT  (ONE_HOT  )
  ) u_valid_demux (
    i_select, slave_if.valid, valid
  );

  pzbcm_mux #(
    .TYPE     (logic    ),
    .ENTRIES  (MASTERS  ),
    .ONE_HOT  (ONE_HOT  )
  ) u_ready_mux (
    i_select, ready, slave_if.ready
  );
endmodule
