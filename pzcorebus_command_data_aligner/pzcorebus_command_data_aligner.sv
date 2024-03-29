//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_command_data_aligner
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG              = '0,
  parameter bit               WAIT_FOR_DATA           = 0,
  parameter bit               THROUGH_NO_DATA_COMMAND = 0,
  parameter bit               RELAX_MODE              = 1,
  parameter bit               SLAVE_FIFO              = 0,
  parameter int               COMMAND_DEPTH           = 2,
  parameter int               DATA_DEPTH              = 2,
  parameter int               RESPONSE_DEPTH          = 0,
  parameter bit               SVA_CHECKER             = 1,
  parameter bit               REQUEST_SVA_CHECKER     = SVA_CHECKER,
  parameter bit               RESPONSE_SVA_CHECKER    = SVA_CHECKER
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
    .BUS_CONFIG               (BUS_CONFIG               ),
    .WAIT_FOR_DATA            (WAIT_FOR_DATA            ),
    .THROUGH_NO_DATA_COMMAND  (THROUGH_NO_DATA_COMMAND  ),
    .RELAX_MODE               (RELAX_MODE               ),
    .SLAVE_FIFO               (SLAVE_FIFO               ),
    .COMMAND_DEPTH            (COMMAND_DEPTH            ),
    .DATA_DEPTH               (DATA_DEPTH               ),
    .SVA_CHECKER              (0                        )
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
    .BUS_CONFIG   (BUS_CONFIG     ),
    .DEPTH        (RESPONSE_DEPTH ),
    .VALID        (SLAVE_FIFO     ),
    .SVA_CHECKER  (0              )
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

//--------------------------------------------------------------
//  SVA checker
//--------------------------------------------------------------
  if (PZCOREBUS_ENABLE_SVA_CHECKER) begin : g_sva
    pzcorebus_sva_checker #(
      .BUS_CONFIG           (BUS_CONFIG           ),
      .REQUEST_SVA_CHECKER  (REQUEST_SVA_CHECKER  ),
      .RESPONSE_SVA_CHECKER (RESPONSE_SVA_CHECKER )
    ) u_sva_checker (
      .i_request_clk    (i_clk      ),
      .i_request_rst_n  (i_rst_n    ),
      .request_bus_if   (slave_if   ),
      .i_response_clk   (i_clk      ),
      .i_response_rst_n (i_rst_n    ),
      .response_bus_if  (master_if  )
    );
  end
endmodule
