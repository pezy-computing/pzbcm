//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzcorebus_connector (
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  always_comb begin
    master_if.mcmd_valid    = slave_if.mcmd_valid;
    slave_if.scmd_accept    = master_if.scmd_accept;
    master_if.mdata_valid   = slave_if.mdata_valid;
    slave_if.sdata_accept   = master_if.sdata_accept;
    master_if.put_request(slave_if.get_request());
  end

  always_comb begin
    slave_if.sresp_valid    = master_if.sresp_valid;
    master_if.mresp_accept  = slave_if.mresp_accept;
    slave_if.put_response(master_if.get_response());
  end
endmodule

module pzcorebus_request_connector (
  interface.request_slave   slave_if,
  interface.request_master  master_if
);
  always_comb begin
    master_if.mcmd_valid    = slave_if.mcmd_valid;
    slave_if.scmd_accept    = master_if.scmd_accept;
    master_if.mdata_valid   = slave_if.mdata_valid;
    slave_if.sdata_accept   = master_if.sdata_accept;
    master_if.put_request(slave_if.get_request());
  end
endmodule

module pzcorebus_response_connector (
  interface.response_slave  slave_if,
  interface.response_master master_if
);
  always_comb begin
    slave_if.sresp_valid    = master_if.sresp_valid;
    master_if.mresp_accept  = slave_if.mresp_accept;
    slave_if.put_response(master_if.get_response());
  end
endmodule

module pzcorebus_array_connector #(
  parameter int N = 1
)(
  pzcorebus_if.slave  slave_if[N],
  pzcorebus_if.master master_if[N]
);
  for (genvar i = 0;i < N;++i) begin : g
    pzcorebus_connector u_connector (
      slave_if[i], master_if[i]
    );
  end
endmodule

module pzcorebus_monitor_connector (
  pzcorebus_if.monitor      in_if,
  pzcorebus_if.monitor_out  out_if
);
  always_comb begin
    out_if.mcmd_valid   = in_if.mcmd_valid;
    out_if.scmd_accept  = in_if.scmd_accept;
    out_if.mdata_valid  = in_if.mdata_valid;
    out_if.sdata_accept = in_if.sdata_accept;
    out_if.put_request(in_if.get_request());
  end

  always_comb begin
    out_if.sresp_valid  = in_if.sresp_valid;
    out_if.mresp_accept = in_if.mresp_accept;
    out_if.put_response(in_if.get_response());
  end
endmodule
