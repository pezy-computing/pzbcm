//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzhsbus_demux
  import  pzbcm_selector_pkg::*;
#(
  parameter int                 MASTERS       = 2,
  parameter pzbcm_selector_type SELECTOR_TYPE = PZBCM_SELECTOR_ONEHOT,
  parameter int                 SELECT_WIDTH  = calc_select_width(SELECTOR_TYPE, MASTERS)
)(
  input var [SELECT_WIDTH-1:0]  i_select,
  pzhsbus_if.slave              slave_if,
  pzhsbus_if.master             master_if[MASTERS]
);
  logic [MASTERS-1:0] ready;
  logic [MASTERS-1:0] valid;

  if (SELECTOR_TYPE == PZBCM_SELECTOR_PRIORITY) begin : g_selector
    logic [MASTERS-1:0] select;

    pzbcm_onehot #(
      .N  (MASTERS  )
    ) u_onehot();

    always_comb begin
      select          = u_onehot.to_onehot(i_select);
      slave_if.ready  = |(select & ready);
      valid           = select & {MASTERS{slave_if.valid}};
    end
  end
  else begin : g_selector
    pzbcm_selector #(
      .WIDTH          (1              ),
      .ENTRIES        (MASTERS        ),
      .SELECTOR_TYPE  (SELECTOR_TYPE  )
    ) u_valid_ready_selector();

    always_comb begin
      slave_if.ready  = u_valid_ready_selector.mux(i_select, ready);
      valid           = u_valid_ready_selector.demux(i_select, slave_if.valid);
    end
  end

  for (genvar i = 0;i < MASTERS;++i) begin : g_master
    always_comb begin
      ready[i]              = master_if[i].ready;
      master_if[i].valid    = valid[i];
      master_if[i].payload  = slave_if.payload;
    end
  end
endmodule
