//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_gate
  import  pzcorebus_pkg::*,
          pzbcm_selector_pkg::PZBCM_SELECTOR_BINARY;
#(
  parameter pzcorebus_config  BUS_CONFIG      = '0,
  parameter bit               RETURN_RESPONSE = 0
)(
  input var           i_clk,
  input var           i_rst_n,
  input var           i_enable,
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  localparam  bit TIE_OFF = (is_memory_profile(BUS_CONFIG)) && (!RETURN_RESPONSE);

  pzcorebus_if #(BUS_CONFIG)  bus_if[2]();

  pzcorebus_demux #(
    .BUS_CONFIG     (BUS_CONFIG             ),
    .MASTERS        (2                      ),
    .SELECTOR_TYPE  (PZBCM_SELECTOR_BINARY  )
  ) u_demux (
    .i_command_select     (i_enable ),
    .i_write_data_select  (i_enable ),
    .i_response_select    (i_enable ),
    .slave_if             (slave_if ),
    .master_if            (bus_if   )
  );

  pzcorebus_connector u_connector (
    .slave_if   (bus_if[1]  ),
    .master_if  (master_if  )
  );

  pzcorebus_dummy_slave #(
    .BUS_CONFIG (BUS_CONFIG ),
    .TIE_OFF    (TIE_OFF    )
  ) u_dummy (
    .i_clk    (i_clk      ),
    .i_rst_n  (i_rst_n    ),
    .slave_if (bus_if[0]  )
  );
endmodule
