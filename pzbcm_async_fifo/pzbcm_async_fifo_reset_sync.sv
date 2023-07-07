//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_async_fifo_reset_sync #(
  parameter bit MERGE_RESET       = '0,
  parameter int RESET_SYNC_STAGES = 2
)(
  input   var is_clk,
  input   var is_rst_n,
  output  var os_rst_n,
  input   var id_clk,
  input   var id_rst_n,
  output  var od_rst_n
);
  if (MERGE_RESET) begin : g_reset
    logic rst_n;

    always_comb begin
      rst_n = is_rst_n & id_rst_n;
    end

    pzbcm_synchronizer #(
      .WIDTH  (1                  ),
      .STAGES (RESET_SYNC_STAGES  )
    ) u_srst_sync (
      .i_clk    (is_clk   ),
      .i_rst_n  (rst_n    ),
      .i_d      ('1       ),
      .o_d      (os_rst_n )
    );

    pzbcm_synchronizer #(
      .WIDTH  (1                  ),
      .STAGES (RESET_SYNC_STAGES  )
    ) u_drst_sync (
      .i_clk    (id_clk   ),
      .i_rst_n  (rst_n    ),
      .i_d      ('1       ),
      .o_d      (od_rst_n )
    );
  end
  else begin : g_reset
    always_comb begin
      os_rst_n  = is_rst_n;
      od_rst_n  = id_rst_n;
    end
  end

endmodule
