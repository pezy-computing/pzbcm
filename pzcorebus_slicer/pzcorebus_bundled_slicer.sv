//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_bundled_slicer
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG        = '0,
  parameter int               REQUEST_CHANNELS  = 1,
  parameter int               RESPONSE_CHANNELS = 1,
  parameter int               STAGES            = 1,
  parameter bit               ASCENDING_ORDER   = 1,
  parameter bit               FIFO_SLICER       = 1,
  parameter bit               DISABLE_MBFF      = 0,
  parameter bit               USE_RESET         = 1,
  parameter bit               REQUEST_VALID     = 1,
  parameter bit               RESPONSE_VALID    = 1
)(
  input var                   i_clk,
  input var                   i_rst_n,
  pzcorebus_bundled_if.slave  slave_if,
  pzcorebus_bundled_if.master master_if
);
  initial begin
    assume (slave_if.REQUEST_CHANNELS   == REQUEST_CHANNELS);
    assume (slave_if.RESPONSE_CHANNELS  == RESPONSE_CHANNELS);
    assume (master_if.REQUEST_CHANNELS  == REQUEST_CHANNELS);
    assume (master_if.RESPONSE_CHANNELS == RESPONSE_CHANNELS);
  end

  localparam  int PACKED_COMMAND_WIDTH    = get_packed_command_width(BUS_CONFIG);
  localparam  int PACKED_WRITE_DATA_WIDTH = get_packed_write_data_width(BUS_CONFIG, 1);
  localparam  int PACKED_RESPONSE_WIDTH   = get_packed_response_width(BUS_CONFIG);

  localparam  int COMMAND_STAGES    = (REQUEST_VALID ) ? STAGES : 0;
  localparam  int WRITE_DATA_STAGES = (REQUEST_VALID ) ? STAGES : 0;
  localparam  int RESPONSE_STAGES   = (RESPONSE_VALID) ? STAGES : 0;

  for (genvar i = 0;i < REQUEST_CHANNELS;++i) begin : g_request
    pzbcm_slicer #(
      .WIDTH            (PACKED_COMMAND_WIDTH ),
      .STAGES           (COMMAND_STAGES       ),
      .ASCENDING_ORDER  (ASCENDING_ORDER      ),
      .FULL_BANDWIDTH   (FIFO_SLICER          ),
      .DISABLE_MBFF     (DISABLE_MBFF         ),
      .USE_RESET        (USE_RESET            )
    ) u_command_slicer (
      .i_clk    (i_clk                    ),
      .i_rst_n  (i_rst_n                  ),
      .i_valid  (slave_if.mcmd_valid[i]   ),
      .o_ready  (slave_if.scmd_accept[i]  ),
      .i_data   (slave_if.mcmd[i]         ),
      .o_valid  (master_if.mcmd_valid[i]  ),
      .i_ready  (master_if.scmd_accept[i] ),
      .o_data   (master_if.mcmd[i]        )
    );

    pzbcm_slicer #(
      .WIDTH            (PACKED_WRITE_DATA_WIDTH  ),
      .STAGES           (WRITE_DATA_STAGES        ),
      .ASCENDING_ORDER  (ASCENDING_ORDER          ),
      .FULL_BANDWIDTH   (FIFO_SLICER              ),
      .DISABLE_MBFF     (DISABLE_MBFF             ),
      .USE_RESET        (USE_RESET                )
    ) u_write_data_slicer (
      .i_clk    (i_clk                      ),
      .i_rst_n  (i_rst_n                    ),
      .i_valid  (slave_if.mdata_valid[i]    ),
      .o_ready  (slave_if.sdata_accept[i]   ),
      .i_data   (slave_if.mdata[i]          ),
      .o_valid  (master_if.mdata_valid[i]   ),
      .i_ready  (master_if.sdata_accept[i]  ),
      .o_data   (master_if.mdata[i]         )
    );
  end

  for (genvar i = 0;i < RESPONSE_CHANNELS;++i) begin : g_response
    pzbcm_slicer #(
      .WIDTH            (PACKED_RESPONSE_WIDTH  ),
      .STAGES           (RESPONSE_STAGES        ),
      .ASCENDING_ORDER  (ASCENDING_ORDER        ),
      .FULL_BANDWIDTH   (FIFO_SLICER            ),
      .DISABLE_MBFF     (DISABLE_MBFF           ),
      .USE_RESET        (USE_RESET              )
    ) u_response_slicer (
      .i_clk    (i_clk                      ),
      .i_rst_n  (i_rst_n                    ),
      .i_valid  (master_if.sresp_valid[i]   ),
      .o_ready  (master_if.mresp_accept[i]  ),
      .i_data   (master_if.sresp[i]         ),
      .o_valid  (slave_if.sresp_valid[i]    ),
      .i_ready  (slave_if.mresp_accept[i]   ),
      .o_data   (slave_if.sresp[i]          )
    );
  end
endmodule
