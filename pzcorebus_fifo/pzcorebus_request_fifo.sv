//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_request_fifo
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               COMMAND_DEPTH     = 2,
  parameter int               COMMAND_THRESHOLD = COMMAND_DEPTH,
  parameter bit               COMMAND_VALID     = 1,
  parameter int               DATA_DEPTH        = 2,
  parameter int               DATA_THRESHOLD    = DATA_DEPTH,
  parameter bit               DATA_VALID        = 1,
  parameter bit               FLAG_FF_OUT       = 1,
  parameter bit               DATA_FF_OUT       = 1
)(
  input   var               i_clk,
  input   var               i_rst_n,
  input   var               i_clear,
  output  var [1:0]         o_empty,
  output  var [1:0]         o_almost_full,
  output  var [1:0]         o_full,
  interface.request_slave   slave_if,
  interface.request_master  master_if
);
  pzcorebus_request_if #(BUS_CONFIG)  bus_if[2]();

  pzcorebus_request_connector u_slave_connector (
    .slave_if   (slave_if   ),
    .master_if  (bus_if[0]  )
  );

  pzcorebus_command_fifo #(
    .BUS_CONFIG   (BUS_CONFIG         ),
    .DEPTH        (COMMAND_DEPTH      ),
    .THRESHOLD    (COMMAND_THRESHOLD  ),
    .VALID        (COMMAND_VALID      ),
    .FLAG_FF_OUT  (FLAG_FF_OUT        ),
    .DATA_FF_OUT  (DATA_FF_OUT        )
  ) u_command_fifo (
    .i_clk          (i_clk            ),
    .i_rst_n        (i_rst_n          ),
    .i_clear        (i_clear          ),
    .o_empty        (o_empty[0]       ),
    .o_almost_full  (o_almost_full[0] ),
    .o_full         (o_full[0]        ),
    .slave_if       (bus_if[0]        ),
    .master_if      (bus_if[1]        )
  );

  pzcorebus_write_data_fifo #(
    .BUS_CONFIG   (BUS_CONFIG     ),
    .DEPTH        (DATA_DEPTH     ),
    .THRESHOLD    (DATA_THRESHOLD ),
    .VALID        (DATA_VALID     ),
    .FLAG_FF_OUT  (FLAG_FF_OUT    ),
    .DATA_FF_OUT  (DATA_FF_OUT    )
  ) u_write_data_fifo (
    .i_clk          (i_clk            ),
    .i_rst_n        (i_rst_n          ),
    .i_clear        (i_clear          ),
    .o_empty        (o_empty[1]       ),
    .o_almost_full  (o_almost_full[1] ),
    .o_full         (o_full[1]        ),
    .slave_if       (bus_if[0]        ),
    .master_if      (bus_if[1]        )
  );

  pzcorebus_request_connector u_master_connector (
    .slave_if   (bus_if[1]  ),
    .master_if  (master_if  )
  );
endmodule
