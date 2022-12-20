//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzhsbus_priority_mux #(
  parameter int SLAVES  = 2
)(
  input var [SLAVES-1:0]  i_select,
  pzhsbus_if.slave        slave_if[SLAVES],
  pzhsbus_if.master       master_if
);
  logic [SLAVES-1:0]  select;

  assign  select  = i_select & (-i_select);
  pzhsbus_mux #(
    .SLAVES   (SLAVES ),
    .ONE_HOT  (1      )
  ) u_mux (
    select, slave_if, master_if
  );
endmodule
