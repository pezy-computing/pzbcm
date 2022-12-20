//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzhsbus_connector (
  pzhsbus_if.slave  slave_if,
  pzhsbus_if.master master_if
);
  always_comb begin
    master_if.valid   = slave_if.valid;
    slave_if.ready    = master_if.ready;
    master_if.payload = slave_if.payload;
  end
endmodule

module pzhsbus_connector_array #(
  parameter N = 1
)(
  pzhsbus_if.slave  slave_if[N],
  pzhsbus_if.master master_if[N]
);
  for (genvar i = 0;i < N;++i) begin : g
    always_comb begin
      master_if[i].valid    = slave_if[i].valid;
      slave_if[i].ready     = master_if[i].ready;
      master_if[i].payload  = slave_if[i].payload;
    end
  end
endmodule
