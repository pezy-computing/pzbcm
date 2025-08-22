//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzhsbus_mux
  import  pzbcm_selector_pkg::*;
#(
  parameter int                 SLAVES        = 2,
  parameter pzbcm_selector_type SELECTOR_TYPE = PZBCM_SELECTOR_ONEHOT,
  parameter int                 SELECT_WIDTH  = calc_select_width(SELECTOR_TYPE, SLAVES)
)(
  input var [SELECT_WIDTH-1:0]  i_select,
  pzhsbus_if.slave              slave_if[SLAVES],
  pzhsbus_if.master             master_if
);
  typedef master_if.__payload __payload;

  logic [SLAVES-1:0]      ready;
  logic [SLAVES-1:0]      valid;
  __payload [SLAVES-1:0]  payload;

  for (genvar i = 0;i < SLAVES;++i) begin : g_slave
    always_comb begin
      slave_if[i].ready = ready[i];
      valid[i]          = slave_if[i].valid;
      payload[i]        = slave_if[i].payload;
    end
  end

  if (SELECTOR_TYPE == PZBCM_SELECTOR_PRIORITY) begin : g_valid_ready
    logic [SLAVES-1:0]  select;

    pzbcm_onehot #(
      .N  (SLAVES )
    ) u_onehot();

    always_comb begin
      select          = u_onehot.to_onehot(i_select);
      ready           = select & {SLAVES{master_if.ready}};
      master_if.valid = |(select & valid);
    end
  end
  else begin : g_master
    pzbcm_selector #(
      .WIDTH          (1              ),
      .ENTRIES        (SLAVES         ),
      .SELECTOR_TYPE  (SELECTOR_TYPE  )
    ) u_selector();

    always_comb begin
      ready           = u_selector.demux(i_select, master_if.ready);
      master_if.valid = u_selector.mux(i_select, valid);
    end
  end

  pzbcm_selector #(
    .TYPE           (__payload      ),
    .ENTRIES        (SLAVES         ),
    .SELECTOR_TYPE  (SELECTOR_TYPE  )
  ) u_payload_selector();

  always_comb begin
    master_if.payload = u_payload_selector.mux(i_select, payload);
  end
endmodule
