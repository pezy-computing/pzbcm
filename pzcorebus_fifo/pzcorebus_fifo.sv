//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_fifo
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG            = '0,
  parameter int               COMMAND_DEPTH         = 2,
  parameter int               COMMAND_THRESHOLD     = COMMAND_DEPTH,
  parameter bit               COMMAND_VALID         = 1,
  parameter int               DATA_DEPTH            = 2,
  parameter int               DATA_THRESHOLD        = DATA_DEPTH,
  parameter bit               DATA_VALID            = 1,
  parameter int               RESPONSE_DEPTH        = 2,
  parameter int               RESPONSE_THRESHOLD    = RESPONSE_DEPTH,
  parameter bit               RESPONSE_VALID        = 1,
  parameter bit               FLAG_FF_OUT           = 1,
  parameter bit               DATA_FF_OUT           = 1,
  parameter bit               RESET_DATA_FF         = 1,
  parameter bit               SVA_CHECKER           = '1,
  parameter bit               REQUEST_SVA_CHECKER   = SVA_CHECKER,
  parameter bit               RESPONSE_SVA_CHECKER  = SVA_CHECKER
)(
  input   var         i_clk,
  input   var         i_rst_n,
  input   var         i_clear,
  output  var [2:0]   o_empty,
  output  var [2:0]   o_almost_full,
  output  var [2:0]   o_full,
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  localparam  int COMMAND_WIDTH   = get_packed_command_width(BUS_CONFIG);
  localparam  int DATA_WIDTH      = get_packed_write_data_width(BUS_CONFIG, 1);
  localparam  int RESPONSE_WIDTH  = get_packed_response_width(BUS_CONFIG);

  logic [1:0]                     scmd_accept;
  logic [1:0]                     mcmd_valid;
  logic [1:0][COMMAND_WIDTH-1:0]  mcmd;
  logic [1:0]                     sdata_accept;
  logic [1:0]                     mdata_valid;
  logic [1:0][DATA_WIDTH-1:0]     mdata;
  logic [1:0]                     mresp_accept;
  logic [1:0]                     sresp_valid;
  logic [1:0][RESPONSE_WIDTH-1:0] sresp;

  always_comb begin
    slave_if.scmd_accept  = scmd_accept[0];
    slave_if.sdata_accept = sdata_accept[0];
    mcmd_valid[0]         = slave_if.mcmd_valid;
    mdata_valid[0]        = slave_if.mdata_valid;
    mcmd[0]               = slave_if.get_packed_command();
    mdata[0]              = slave_if.get_packed_write_data();
  end

  always_comb begin
    mresp_accept[0]       = slave_if.mresp_accept;
    slave_if.sresp_valid  = sresp_valid[0];
    slave_if.put_packed_response(sresp[0]);
  end

  always_comb begin
    scmd_accept[1]        = master_if.scmd_accept;
    sdata_accept[1]       = master_if.sdata_accept;
    master_if.mcmd_valid  = mcmd_valid[1];
    master_if.mdata_valid = mdata_valid[1];
    master_if.put_packed_command(mcmd[1]);
    master_if.put_packed_write_data(mdata[1]);
  end

  always_comb begin
    master_if.mresp_accept  = mresp_accept[1];
    sresp_valid[1]          = master_if.sresp_valid;
    sresp[1]                = master_if.get_packed_response();
  end

  if (COMMAND_VALID && (COMMAND_DEPTH >= 2)) begin : g_command
    logic [2:0] status;

    always_comb begin
      o_empty[0]        = status[0];
      o_almost_full[0]  = status[1];
      o_full[0]         = status[2];
    end

    always_comb begin
      scmd_accept[0]  = !status[2];
      mcmd_valid[1]   = !status[0];
    end

    pzbcm_fifo #(
      .WIDTH          (COMMAND_WIDTH      ),
      .DEPTH          (COMMAND_DEPTH      ),
      .THRESHOLD      (COMMAND_THRESHOLD  ),
      .FLAG_FF_OUT    (FLAG_FF_OUT        ),
      .DATA_FF_OUT    (DATA_FF_OUT        ),
      .RESET_DATA_FF  (RESET_DATA_FF      )
    ) u_fifo (
      .i_clk          (i_clk          ),
      .i_rst_n        (i_rst_n        ),
      .i_clear        (i_clear        ),
      .o_empty        (status[0]      ),
      .o_almost_full  (status[1]      ),
      .o_full         (status[2]      ),
      .o_word_count   (),
      .i_push         (mcmd_valid[0]  ),
      .i_data         (mcmd[0]        ),
      .i_pop          (scmd_accept[1] ),
      .o_data         (mcmd[1]        )
    );
  end
  else begin : g_command
    always_comb begin
      o_empty[0]        = '1;
      o_almost_full[0]  = '0;
      o_full[0]         = '0;
    end

    always_comb begin
      scmd_accept[0]  = scmd_accept[1];
      mcmd_valid[1]   = mcmd_valid[0];
      mcmd[1]         = mcmd[0];
    end
  end

  if (DATA_VALID && (DATA_DEPTH >= 2) && is_memory_profile(BUS_CONFIG)) begin : g_write_data
    logic [2:0] status;

    always_comb begin
      o_empty[1]        = status[0];
      o_almost_full[1]  = status[1];
      o_full[1]         = status[2];
    end

    always_comb begin
      sdata_accept[0] = !status[2];
      mdata_valid[1]  = !status[0];
    end

    pzbcm_fifo #(
      .WIDTH          (DATA_WIDTH     ),
      .DEPTH          (DATA_DEPTH     ),
      .THRESHOLD      (DATA_THRESHOLD ),
      .FLAG_FF_OUT    (FLAG_FF_OUT    ),
      .DATA_FF_OUT    (DATA_FF_OUT    ),
      .RESET_DATA_FF  (RESET_DATA_FF  )
    ) u_fifo (
      .i_clk          (i_clk            ),
      .i_rst_n        (i_rst_n          ),
      .i_clear        (i_clear          ),
      .o_empty        (status[0]        ),
      .o_almost_full  (status[1]        ),
      .o_full         (status[2]        ),
      .o_word_count   (),
      .i_push         (mdata_valid[0]   ),
      .i_data         (mdata[0]         ),
      .i_pop          (sdata_accept[1]  ),
      .o_data         (mdata[1]         )
    );
  end
  else begin : g_write_data
    always_comb begin
      o_empty[1]        = '1;
      o_almost_full[1]  = '0;
      o_full[1]         = '0;
    end

    always_comb begin
      sdata_accept[0] = sdata_accept[1];
      mdata_valid[1]  = mdata_valid[0];
      mdata[1]        = mdata[0];
    end
  end

  if (RESPONSE_VALID && (RESPONSE_DEPTH >= 2)) begin : g_response
    logic [2:0] status;

    always_comb begin
      o_empty[2]        = status[0];
      o_almost_full[2]  = status[1];
      o_full[2]         = status[2];
    end

    always_comb begin
      mresp_accept[1] = !status[2];
      sresp_valid[0]  = !status[0];
    end

    pzbcm_fifo #(
      .WIDTH          (RESPONSE_WIDTH     ),
      .DEPTH          (RESPONSE_DEPTH     ),
      .THRESHOLD      (RESPONSE_THRESHOLD ),
      .FLAG_FF_OUT    (FLAG_FF_OUT        ),
      .DATA_FF_OUT    (DATA_FF_OUT        ),
      .RESET_DATA_FF  (RESET_DATA_FF      )
    ) u_fifo (
      .i_clk          (i_clk            ),
      .i_rst_n        (i_rst_n          ),
      .i_clear        (i_clear          ),
      .o_empty        (status[0]        ),
      .o_almost_full  (status[1]        ),
      .o_full         (status[2]        ),
      .o_word_count   (),
      .i_push         (sresp_valid[1]   ),
      .i_data         (sresp[1]         ),
      .i_pop          (mresp_accept[0]  ),
      .o_data         (sresp[0]         )
    );
  end
  else begin : g_response
    always_comb begin
      o_empty[2]        = '1;
      o_almost_full[2]  = '0;
      o_full[2]         = '0;
    end

    always_comb begin
      mresp_accept[1] = mresp_accept[0];
      sresp_valid[0]  = sresp_valid[1];
      sresp[0]        = sresp[1];
    end
  end

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
