//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_slicer
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG            = '0,
  parameter int               STAGES                = 1,
  parameter bit               ASCENDING_ORDER       = 1,
  parameter bit               FIFO_SLICER           = 1,
  parameter bit               DISABLE_MBFF          = 0,
  parameter bit               USE_RESET             = 1,
  parameter bit               REQUEST_VALID         = 1,
  parameter bit               RESPONSE_VALID        = 1,
  parameter bit               SVA_CHECKER           = 1,
  parameter bit               REQUEST_SVA_CHECKER   = SVA_CHECKER,
  parameter bit               RESPONSE_SVA_CHECKER  = SVA_CHECKER
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  localparam  int COMMAND_WIDTH     = get_packed_command_width(BUS_CONFIG);
  localparam  int WRITE_DATA_WIDTH  = get_packed_write_data_width(BUS_CONFIG, 1);
  localparam  int RESPONSE_WIDTH    = get_packed_response_width(BUS_CONFIG);

  localparam  int COMMAND_STAGES    = (REQUEST_VALID) ? STAGES : 0;
  localparam  int WRITE_DATA_STAGES = (REQUEST_VALID && is_memory_profile(BUS_CONFIG)) ? STAGES : 0;
  localparam  int RESPONSE_STAGES   = (RESPONSE_VALID) ? STAGES : 0;

  logic [COMMAND_WIDTH-1:0]     slave_command;
  logic [COMMAND_WIDTH-1:0]     master_command;
  logic [WRITE_DATA_WIDTH-1:0]  slave_write_data;
  logic [WRITE_DATA_WIDTH-1:0]  master_write_data;
  logic [RESPONSE_WIDTH-1:0]    slave_response;
  logic [RESPONSE_WIDTH-1:0]    master_response;

  always_comb begin
    slave_command     = slave_if.get_packed_command();
    slave_write_data  = slave_if.get_packed_write_data();
  end

  always_comb begin
    slave_if.put_packed_response(slave_response);
  end

  always_comb begin
    master_if.put_packed_command(master_command);
    master_if.put_packed_write_data(master_write_data);
  end

  always_comb begin
    master_response = master_if.get_packed_response();
  end

  pzbcm_slicer #(
    .WIDTH            (COMMAND_WIDTH    ),
    .STAGES           (COMMAND_STAGES   ),
    .ASCENDING_ORDER  (ASCENDING_ORDER  ),
    .FULL_BANDWIDTH   (FIFO_SLICER      ),
    .DISABLE_MBFF     (DISABLE_MBFF     ),
    .USE_RESET        (USE_RESET        )
  ) u_command_slicer (
    .i_clk    (i_clk                  ),
    .i_rst_n  (i_rst_n                ),
    .i_valid  (slave_if.mcmd_valid    ),
    .o_ready  (slave_if.scmd_accept   ),
    .i_data   (slave_command          ),
    .o_valid  (master_if.mcmd_valid   ),
    .i_ready  (master_if.scmd_accept  ),
    .o_data   (master_command         )
  );

  pzbcm_slicer #(
    .WIDTH            (WRITE_DATA_WIDTH   ),
    .STAGES           (WRITE_DATA_STAGES  ),
    .ASCENDING_ORDER  (ASCENDING_ORDER    ),
    .FULL_BANDWIDTH   (FIFO_SLICER        ),
    .DISABLE_MBFF     (DISABLE_MBFF       ),
    .USE_RESET        (USE_RESET          )
  ) u_write_data_slicer (
    .i_clk    (i_clk                  ),
    .i_rst_n  (i_rst_n                ),
    .i_valid  (slave_if.mdata_valid   ),
    .o_ready  (slave_if.sdata_accept  ),
    .i_data   (slave_write_data       ),
    .o_valid  (master_if.mdata_valid  ),
    .i_ready  (master_if.sdata_accept ),
    .o_data   (master_write_data      )
  );

  pzbcm_slicer #(
    .WIDTH            (RESPONSE_WIDTH   ),
    .STAGES           (RESPONSE_STAGES  ),
    .ASCENDING_ORDER  (ASCENDING_ORDER  ),
    .FULL_BANDWIDTH   (FIFO_SLICER      ),
    .DISABLE_MBFF     (DISABLE_MBFF     ),
    .USE_RESET        (USE_RESET        )
  ) u_response_slicer (
    .i_clk    (i_clk                  ),
    .i_rst_n  (i_rst_n                ),
    .i_valid  (master_if.sresp_valid  ),
    .o_ready  (master_if.mresp_accept ),
    .i_data   (master_response        ),
    .o_valid  (slave_if.sresp_valid   ),
    .i_ready  (slave_if.mresp_accept  ),
    .o_data   (slave_response         )
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
