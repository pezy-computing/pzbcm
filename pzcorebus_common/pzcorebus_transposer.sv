//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_transposer #(
  parameter int M = 1,
  parameter int N = 1
)(
  pzcorebus_if.slave  slave_if[M*N],
  pzcorebus_if.master master_if[N*M]
);
  for (genvar i = 0;i < M;++i) begin : g
    for (genvar j = 0;j < N;++j) begin : g
      pzcorebus_connector u_connector (
        .slave_if   (slave_if[N*i+j]  ),
        .master_if  (master_if[M*j+i] )
      );
    end
  end
endmodule

module pzcorebus_request_transposer #(
  parameter int M = 1,
  parameter int N = 1
)(
  interface.request_slave   slave_if[M*N],
  interface.request_master  master_if[N*M]
);
  for (genvar i = 0;i < M;++i) begin : g
    for (genvar j = 0;j < N;++j) begin : g
      pzcorebus_request_connector u_connector (
        .slave_if   (slave_if[N*i+j]  ),
        .master_if  (master_if[M*j+i] )
      );
    end
  end
endmodule

module pzcorebus_response_transposer #(
  parameter int M = 1,
  parameter int N = 1
)(
  interface.response_slave  slave_if[M*N],
  interface.response_master master_if[N*M]
);
  for (genvar i = 0;i < M;++i) begin : g
    for (genvar j = 0;j < N;++j) begin : g
      pzcorebus_response_connector u_connector (
        .slave_if   (slave_if[N*i+j]  ),
        .master_if  (master_if[M*j+i] )
      );
    end
  end
endmodule
