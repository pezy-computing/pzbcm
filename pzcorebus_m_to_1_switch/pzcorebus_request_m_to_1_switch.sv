//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_request_m_to_1_switch
  import  pzcorebus_pkg::*,
          pzbcm_arbiter_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config          BUS_CONFIG        = '0,
  parameter int                       SLAVES            = 2,
  parameter bit [1:0]                 ENABLE_ARBITER    = 2'b01,
  parameter int                       PRIORITY_WIDTH    = 0,
  parameter int                       WEIGHT_WIDTH      = 0,
  parameter pzbcm_arbiter_weight_list WEIGHT            = '1,
  parameter bit                       WAIT_FOR_DATA     = 0,
  parameter bit                       WAIT_FOR_RESPONSE = 0,
  parameter bit                       SLAVE_FIFO        = '0,
  parameter bit                       MASTER_FIFO       = '0,
  parameter int                       COMMAND_DEPTH     = 2,
  parameter int                       DATA_DEPTH        = 2,
  parameter bit                       ALIGN_OUT         = 0
)(
  input   var                       i_clk,
  input   var                       i_rst_n,
  input   var pzbcm_arbiter_config  i_arbiter_config,
  output  var [SLAVES-1:0]          o_response_select,
  input   var                       i_response_ack,
  interface.request_slave           slave_if[SLAVES],
  interface.request_master          master_if
);
  pzcorebus_request_if #(BUS_CONFIG)  aligner_if[SLAVES]();
  pzcorebus_request_if #(BUS_CONFIG)  switch_if[SLAVES+1]();

//--------------------------------------------------------------
//  Slave Command/Data Aligner
//--------------------------------------------------------------
  for (genvar i = 0;i < SLAVES;++i) begin : g_slave_aligner
    if (is_memory_profile(BUS_CONFIG)) begin : g
      pzcorebus_command_data_aligner_core #(
        .BUS_CONFIG     (BUS_CONFIG     ),
        .WAIT_FOR_DATA  (WAIT_FOR_DATA  ),
        .RELAX_MODE     (1              ),
        .SLAVE_FIFO     (SLAVE_FIFO     ),
        .COMMAND_DEPTH  (COMMAND_DEPTH  ),
        .DATA_DEPTH     (DATA_DEPTH     )
      ) u_aligner (
        .i_clk        (i_clk          ),
        .i_rst_n      (i_rst_n        ),
        .o_mcmd_done  (),
        .o_mdata_done (),
        .o_mcmd       (),
        .o_mid        (),
        .o_maddr      (),
        .o_minfo      (),
        .slave_if     (slave_if[i]    ),
        .master_if    (aligner_if[i]  )
      );
    end
    else begin : g
      pzcorebus_request_fifo #(
        .BUS_CONFIG     (BUS_CONFIG     ),
        .COMMAND_DEPTH  (COMMAND_DEPTH  ),
        .COMMAND_VALID  (SLAVE_FIFO     ),
        .DATA_DEPTH     (DATA_DEPTH     ),
        .DATA_VALID     (SLAVE_FIFO     )
      ) u_slave_fifo (
        .i_clk          (i_clk          ),
        .i_rst_n        (i_rst_n        ),
        .i_clear        (1'b0           ),
        .o_empty        (),
        .o_almost_full  (),
        .o_full         (),
        .slave_if       (slave_if[i]    ),
        .master_if      (aligner_if[i]  )
      );
    end
  end

//--------------------------------------------------------------
//  Switch
//--------------------------------------------------------------
  logic [SLAVES-1:0]  request_valid;
  logic [SLAVES-1:0]  request_grant;
  logic               request_free;
  logic               response_idle;

  for (genvar i = 0;i < SLAVES;++i) begin : g_request
    always_comb begin
      aligner_if[i].scmd_accept = response_idle && switch_if[i].scmd_accept;
      switch_if[i].mcmd_valid   = response_idle && aligner_if[i].mcmd_valid;
      switch_if[i].put_command(aligner_if[i].get_command());
    end

    always_comb begin
      aligner_if[i].sdata_accept  = switch_if[i].sdata_accept;
      switch_if[i].mdata_valid    = aligner_if[i].mdata_valid;
      switch_if[i].put_write_data(aligner_if[i].get_write_data());
    end

    always_comb begin
      request_valid[i]  = switch_if[i].mcmd_valid;
    end
  end

  if (is_memory_profile(BUS_CONFIG)) begin : g_request_free
    logic [3:0] access_done;
    logic       command_done;
    logic       data_done;

    always_comb begin
      access_done[0]  = switch_if[SLAVES].command_no_data_ack();
      access_done[1]  = switch_if[SLAVES].command_with_data_ack() && switch_if[SLAVES].write_data_last_ack();
      access_done[2]  = switch_if[SLAVES].command_with_data_ack() && data_done;
      access_done[3]  = switch_if[SLAVES].write_data_last_ack() && command_done;
      request_free    = access_done != '0;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        command_done  <= '0;
        data_done     <= '0;
      end
      else if (request_free) begin
        command_done  <= '0;
        data_done     <= '0;
      end
      else if (switch_if[SLAVES].command_with_data_ack()) begin
        command_done  <= '1;
        data_done     <= '0;
      end
      else if (switch_if[SLAVES].write_data_last_ack()) begin
        command_done  <= '0;
        data_done     <= '1;
      end
    end
  end
  else begin : g_request_free
    always_comb begin
      request_free  = switch_if[SLAVES].command_ack();
    end
  end

  pzbcm_arbiter #(
    .REQUESTS       (SLAVES         ),
    .ENABLE_ARBITER (ENABLE_ARBITER ),
    .PRIORITY_WIDTH (PRIORITY_WIDTH ),
    .WEIGHT_WIDTH   (WEIGHT_WIDTH   ),
    .WEIGHT         (WEIGHT         ),
    .ONEHOT_GRANT   (1              ),
    .KEEP_RESULT    (1              )
  ) u_arbiter (
    .i_clk      (i_clk                  ),
    .i_rst_n    (i_rst_n                ),
    .i_config   (i_arbiter_config       ),
    .i_request  (request_valid          ),
    .o_grant    (request_grant          ),
    .i_free     ({SLAVES{request_free}} )
  );

  pzcorebus_request_mux #(
    .BUS_CONFIG     (BUS_CONFIG             ),
    .SLAVES         (SLAVES                 ),
    .SELECTOR_TYPE  (PZBCM_SELECTOR_ONEHOT  )
  ) u_mux (
    .i_command_select     (request_grant          ),
    .i_write_data_select  (request_grant          ),
    .slave_if             (switch_if[0:SLAVES-1]  ),
    .master_if            (switch_if[SLAVES]      )
  );

  if (WAIT_FOR_RESPONSE) begin : g_response_select
    logic [SLAVES-1:0]  response_select;

    always_comb begin
      o_response_select = response_select;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        response_idle <= '1;
      end
      else if (i_response_ack) begin
        response_idle <= '1;
      end
      else if (switch_if[SLAVES].command_non_posted_ack()) begin
        response_idle <= '0;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        response_select <= '0;
      end
      else if (switch_if[SLAVES].command_non_posted_ack()) begin
        response_select <= request_grant;
      end
    end
  end
  else begin : g_response_select
    always_comb begin
      o_response_select = '0;
    end

    always_comb begin
      response_idle = '1;
    end
  end

//--------------------------------------------------------------
//  Master Command/Data Alignment
//--------------------------------------------------------------
  if (is_memory_profile(BUS_CONFIG) && ALIGN_OUT && MASTER_FIFO) begin : g_master_aligner
    pzcorebus_command_data_aligner #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .RELAX_MODE     (1              ),
      .SLAVE_FIFO     (1              ),
      .COMMAND_DEPTH  (COMMAND_DEPTH  ),
      .DATA_DEPTH     (DATA_DEPTH     )
    ) u_aligner (
      .i_clk      (i_clk              ),
      .i_rst_n    (i_rst_n            ),
      .slave_if   (switch_if[SLAVES]  ),
      .master_if  (master_if          )
    );
  end
  else begin : g_master_aligner
    pzcorebus_request_fifo #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .COMMAND_DEPTH  (COMMAND_DEPTH  ),
      .COMMAND_VALID  (MASTER_FIFO    ),
      .DATA_DEPTH     (DATA_DEPTH     ),
      .DATA_VALID     (MASTER_FIFO    )
    ) u_fifo (
      .i_clk          (i_clk              ),
      .i_rst_n        (i_rst_n            ),
      .i_clear        ('0                 ),
      .o_empty        (),
      .o_almost_full  (),
      .o_full         (),
      .slave_if       (switch_if[SLAVES]  ),
      .master_if      (master_if          )
    );
  end
endmodule
