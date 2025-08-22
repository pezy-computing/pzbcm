//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzvbus_demux #(
  parameter   int MASTERS       = 2,
  parameter   bit ONE_HOT       = 1,
  localparam  int SELECT_WIDTH  = (ONE_HOT) ? MASTERS : $clog2(MASTERS)
)(
  input var [SELECT_WIDTH-1:0]  i_select,
  pzvbus_if.slave               slave_if,
  pzvbus_if.master              master_if[MASTERS]
);
  logic valid[MASTERS];

  for (genvar i = 0;i < MASTERS;++i) begin : g
    assign  master_if[i].valid    = valid[i];
    assign  master_if[i].payload  = slave_if.payload;
  end

  pzbcm_demux #(
    .TYPE     (logic    ),
    .ENTRIES  (MASTERS  ),
    .ONE_HOT  (ONE_HOT  )
  ) u_valid_demux (
    i_select, slave_if.valid, valid
  );
endmodule
