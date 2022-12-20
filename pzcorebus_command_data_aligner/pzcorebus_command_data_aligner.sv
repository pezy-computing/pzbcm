//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_command_data_aligner
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG      = '0,
  parameter bit               WAIT_FOR_DATA   = 0,
  parameter bit               RELAX_MODE      = 1,
  parameter bit               SLAVE_FIFO      = 0,
  parameter int               COMMAND_DEPTH   = 2,
  parameter int               DATA_DEPTH      = 2,
  parameter int               RESPONSE_DEPTH  = 0
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  pzcorebus_if #(BUS_CONFIG)  bus_if[2]();

  pzcorebus_connector u_slave_connector (
    .slave_if   (slave_if   ),
    .master_if  (bus_if[0]  )
  );

  pzcorebus_command_data_aligner_core #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .WAIT_FOR_DATA  (WAIT_FOR_DATA  ),
    .RELAX_MODE     (RELAX_MODE     ),
    .SLAVE_FIFO     (SLAVE_FIFO     ),
    .COMMAND_DEPTH  (COMMAND_DEPTH  ),
    .DATA_DEPTH     (DATA_DEPTH     )
  ) u_aligner_core (
    .i_clk        (i_clk      ),
    .i_rst_n      (i_rst_n    ),
    .o_mcmd_done  (),
    .o_mdata_done (),
    .o_mcmd       (),
    .o_mid        (),
    .o_maddr      (),
    .o_minfo      (),
    .slave_if     (bus_if[0]  ),
    .master_if    (bus_if[1]  )
  );

  pzcorebus_response_fifo #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .RESPONSE_DEPTH (RESPONSE_DEPTH ),
    .RESPONSE_VALID (SLAVE_FIFO     )
  ) u_response_fifo (
    .i_clk          (i_clk      ),
    .i_rst_n        (i_rst_n    ),
    .i_clear        ('0         ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (bus_if[0]  ),
    .master_if      (bus_if[1]  )
  );

  pzcorebus_connector u_master_connector (
    .slave_if   (bus_if[1]  ),
    .master_if  (master_if  )
  );
endmodule
