//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_response_slicer
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG      = '0,
  parameter int               STAGES          = 1,
  parameter bit               ASCENDING_ORDER = 1,
  parameter bit               FIFO_SLICER     = 1,
  parameter bit               DISABLE_MBFF    = 0,
  parameter bit               USE_RESET       = 1,
  parameter bit               SVA_CHECKER     = 1
)(
  input var                 i_clk,
  input var                 i_rst_n,
  interface.response_slave  slave_if,
  interface.response_master master_if
);
  localparam  int RESPONSE_WIDTH    = get_packed_response_width(BUS_CONFIG);

  logic [RESPONSE_WIDTH-1:0]  slave_sresp;
  logic [RESPONSE_WIDTH-1:0]  master_sresp;

  always_comb begin
    master_sresp  = master_if.get_packed_response();
  end

  always_comb begin
    slave_if.put_packed_response(slave_sresp);
  end

  pzbcm_slicer #(
    .WIDTH            (RESPONSE_WIDTH   ),
    .STAGES           (STAGES           ),
    .ASCENDING_ORDER  (ASCENDING_ORDER  ),
    .FULL_BANDWIDTH   (FIFO_SLICER      ),
    .DISABLE_MBFF     (DISABLE_MBFF     ),
    .USE_RESET        (USE_RESET        )
  ) u_response_slicer (
    .i_clk    (i_clk                  ),
    .i_rst_n  (i_rst_n                ),
    .i_valid  (master_if.sresp_valid  ),
    .o_ready  (master_if.mresp_accept ),
    .i_data   (master_sresp           ),
    .o_valid  (slave_if.sresp_valid   ),
    .i_ready  (slave_if.mresp_accept  ),
    .o_data   (slave_sresp            )
  );

//--------------------------------------------------------------
//  SVA checker
//--------------------------------------------------------------
  if (PZCOREBUS_ENABLE_SVA_CHECKER) begin : g_sva
    pzcorebus_response_sva_checker #(
      .BUS_CONFIG   (BUS_CONFIG   ),
      .SVA_CHECKER  (SVA_CHECKER  )
    ) u_sva_checker (
      .i_clk    (i_clk      ),
      .i_rst_n  (i_rst_n    ),
      .bus_if   (master_if  )
    );
  end
endmodule
