//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_upsizer
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  SLAVE_CONFIG    = '0,
  parameter pzcorebus_config  MASTER_CONFIG   = '0,
  parameter bit [1:0]         SLAVE_FIFO      = '0,
  parameter bit [1:0]         MASTER_FIFO     = '0,
  parameter int               COMMAND_DEPTH   = 2,
  parameter int               DATA_DEPTH      = 2,
  parameter int               RESPONSE_DEPTH  = 2
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  localparam  int CONVERSION_RATIO  = MASTER_CONFIG.data_width / SLAVE_CONFIG.data_width;

  pzcorebus_if #(SLAVE_CONFIG)  slave_fifo_if();
  pzcorebus_if #(SLAVE_CONFIG)  aligner_if();
  pzcorebus_if #(MASTER_CONFIG) converter_if();

//--------------------------------------------------------------
//  Slave FIFO
//--------------------------------------------------------------
  localparam  int SLAVE_COMMAND_DEPTH   = (SLAVE_FIFO[0]) ? COMMAND_DEPTH  : 0;
  localparam  int SLAVE_DATA_DEPTH      = (SLAVE_FIFO[0]) ? DATA_DEPTH     : 0;
  localparam  int SLAVE_RESPONSE_DEPTH  = (SLAVE_FIFO[1]) ? RESPONSE_DEPTH : 0;

  pzcorebus_fifo #(
    .BUS_CONFIG     (SLAVE_CONFIG         ),
    .COMMAND_DEPTH  (SLAVE_COMMAND_DEPTH  ),
    .DATA_DEPTH     (SLAVE_DATA_DEPTH     ),
    .RESPONSE_DEPTH (SLAVE_RESPONSE_DEPTH )
  ) u_slave_fifo (
    .i_clk          (i_clk          ),
    .i_rst_n        (i_rst_n        ),
    .i_clear        ('0             ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (slave_if       ),
    .master_if      (slave_fifo_if  )
  );

//--------------------------------------------------------------
//  Command/Data Aligner
//--------------------------------------------------------------
  pzcorebus_command_data_aligner #(
    .BUS_CONFIG (SLAVE_CONFIG ),
    .RELAX_MODE (1            )
  ) u_aligner (
    .i_clk      (i_clk          ),
    .i_rst_n    (i_rst_n        ),
    .slave_if   (slave_fifo_if  ),
    .master_if  (aligner_if     )
  );

//--------------------------------------------------------------
//  Data Width Conversion
//--------------------------------------------------------------
  pzcorebus_upsizer_request_path #(
    .SLAVE_CONFIG     (SLAVE_CONFIG     ),
    .MASTER_CONFIG    (MASTER_CONFIG    ),
    .CONVERSION_RATIO (CONVERSION_RATIO )
  ) u_request_path (
    .i_clk      (i_clk        ),
    .i_rst_n    (i_rst_n      ),
    .slave_if   (aligner_if   ),
    .master_if  (converter_if )
  );

  pzcorebus_upsizer_response_path #(
    .SLAVE_CONFIG   (SLAVE_CONFIG   ),
    .MASTER_CONFIG  (MASTER_CONFIG  )
  ) u_response_path (
    .i_clk      (i_clk        ),
    .i_rst_n    (i_rst_n      ),
    .slave_if   (aligner_if   ),
    .master_if  (converter_if )
  );

//--------------------------------------------------------------
//  Master FIFO
//--------------------------------------------------------------
  localparam  int MASTER_FIFO_DEPTH[3]  =
    (MASTER_FIFO) ? '{COMMAND_DEPTH, DATA_DEPTH, RESPONSE_DEPTH}
                  : '{0            , 0         , 0             };

  localparam  int MASTER_COMMAND_DEPTH  = (MASTER_FIFO[0]) ? COMMAND_DEPTH  : 0;
  localparam  int MASTER_DATA_DEPTH     = (MASTER_FIFO[0]) ? DATA_DEPTH     : 0;
  localparam  int MASTER_RESPONSE_DEPTH = (MASTER_FIFO[1]) ? RESPONSE_DEPTH : 0;

  pzcorebus_fifo #(
    .BUS_CONFIG     (MASTER_CONFIG          ),
    .COMMAND_DEPTH  (MASTER_COMMAND_DEPTH   ),
    .DATA_DEPTH     (MASTER_DATA_DEPTH      ),
    .RESPONSE_DEPTH (MASTER_RESPONSE_DEPTH  )
  ) u_master_fifo (
    .i_clk          (i_clk        ),
    .i_rst_n        (i_rst_n      ),
    .i_clear        ('0           ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (converter_if ),
    .master_if      (master_if    )
  );
endmodule
