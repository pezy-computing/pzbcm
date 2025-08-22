//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//
//========================================
module pzcorebus_dummy
  import  pzcorebus_pkg::*,
          pzcorebus_dummy_pkg::*;
#(
  parameter pzcorebus_config                BUS_CONFIG      = '0,
  parameter bit                             TIE_OFF         = 0,
  parameter bit                             ERROR           = 1,
  parameter bit [31:0]                      ERROR_DATA      = get_error_data(BUS_CONFIG),
  parameter bit [BUS_CONFIG.data_width-1:0] READ_DATA       = {BUS_CONFIG.data_width/32{ERROR_DATA}},
  parameter bit                             ENABLE_WARNING  = 1
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  pzcorebus_dummy_slave #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .TIE_OFF        (TIE_OFF        ),
    .ERROR          (ERROR          ),
    .ERROR_DATA     (ERROR_DATA     ),
    .READ_DATA      (READ_DATA      ),
    .ENABLE_WARNING (ENABLE_WARNING )
  ) u_slave (
    .i_clk    (i_clk    ),
    .i_rst_n  (i_rst_n  ),
    .slave_if (slave_if )
  );

  pzcorebus_dummy_master u_master (
    .master_if  (master_if  )
  );
endmodule

module pzcorebus_array_dummy
  import  pzcorebus_pkg::*,
          pzcorebus_dummy_pkg::*;
#(
  parameter pzcorebus_config                BUS_CONFIG      = '0,
  parameter int                             SLAVES          = 2,
  parameter int                             MASTERS         = SLAVES,
  parameter bit                             TIE_OFF         = 0,
  parameter bit                             ERROR           = 1,
  parameter bit [31:0]                      ERROR_DATA      = get_error_data(BUS_CONFIG),
  parameter bit [BUS_CONFIG.data_width-1:0] READ_DATA       = {BUS_CONFIG.data_width/32{ERROR_DATA}},
  parameter bit                             ENABLE_WARNING  = 1
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if[SLAVES],
  pzcorebus_if.master master_if[MASTERS]
);
  for (genvar i = 0;i < SLAVES;++i) begin : g_slave
    pzcorebus_dummy_slave #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .TIE_OFF        (TIE_OFF        ),
      .ERROR          (ERROR          ),
      .ERROR_DATA     (ERROR_DATA     ),
      .READ_DATA      (READ_DATA      ),
      .ENABLE_WARNING (ENABLE_WARNING )
    ) u_slave (
      .i_clk    (i_clk        ),
      .i_rst_n  (i_rst_n      ),
      .slave_if (slave_if[i]  )
    );
  end

  for (genvar i = 0;i < MASTERS;++i) begin : g_master
    pzcorebus_dummy_master u_master (
      .master_if  (master_if[i] )
    );
  end
endmodule
