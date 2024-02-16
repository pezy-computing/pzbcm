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
  parameter bit                       ALIGN_OUT         = 0,
  parameter bit                       SVA_CHECKER       = 1
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
        .BUS_CONFIG               (BUS_CONFIG     ),
        .WAIT_FOR_DATA            (WAIT_FOR_DATA  ),
        .RELAX_MODE               (1              ),
        .THROUGH_NO_DATA_COMMAND  (1              ),
        .SLAVE_FIFO               (SLAVE_FIFO     ),
        .COMMAND_DEPTH            (COMMAND_DEPTH  ),
        .DATA_DEPTH               (DATA_DEPTH     ),
        .SVA_CHECKER              (SVA_CHECKER    )
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
        .DATA_VALID     (SLAVE_FIFO     ),
        .SVA_CHECKER    (SVA_CHECKER    )
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
  logic [SLAVES-1:0]  command_valid;
  logic [SLAVES-1:0]  command_grand;
  logic [SLAVES-1:0]  command_ack;
  logic               command_done;
  logic [SLAVES-1:0]  data_grant;
  logic               response_idle;

  for (genvar i = 0;i < SLAVES;++i) begin : g_request
    logic command_ready;

    always_comb begin
      command_ready =
        response_idle &&
        ((!command_done) || switch_if[i].is_command_no_data());

      aligner_if[i].scmd_accept = command_ready && switch_if[i].scmd_accept;
      switch_if[i].mcmd_valid   = command_ready && aligner_if[i].mcmd_valid;
      switch_if[i].put_command(aligner_if[i].get_command());
    end

    always_comb begin
      aligner_if[i].sdata_accept  = switch_if[i].sdata_accept;
      switch_if[i].mdata_valid    = aligner_if[i].mdata_valid;
      switch_if[i].put_write_data(aligner_if[i].get_write_data());
    end

    always_comb begin
      command_valid[i]  = switch_if[i].mcmd_valid;
      command_ack[i]    = switch_if[i].command_ack();
    end
  end

  if (is_memory_profile(BUS_CONFIG)) begin : g_data_grant
    logic [2:0]         done;
    logic               data_done;
    logic [SLAVES-1:0]  grant_latched;

    always_comb begin
      done[0] = switch_if[SLAVES].command_with_data_ack() && switch_if[SLAVES].write_data_last_ack();
      done[1] = switch_if[SLAVES].command_with_data_ack() && data_done;
      done[2] = switch_if[SLAVES].write_data_last_ack() && command_done;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        command_done  <= '0;
        data_done     <= '0;
      end
      else if (done != '0) begin
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

    always_comb begin
      if (command_done) begin
        data_grant  = grant_latched;
      end
      else begin
        data_grant  = command_grand;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        grant_latched <= '0;
      end
      else if (switch_if[SLAVES].command_with_data_ack()) begin
        grant_latched <= command_grand;
      end
    end
  end
  else begin : g_data_grant
    always_comb begin
      command_done  = '0;
      data_grant    = '0;
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
    .i_clk      (i_clk            ),
    .i_rst_n    (i_rst_n          ),
    .i_config   (i_arbiter_config ),
    .i_request  (command_valid    ),
    .o_grant    (command_grand    ),
    .i_free     (command_ack      )
  );

  pzcorebus_request_mux #(
    .BUS_CONFIG     (BUS_CONFIG             ),
    .SLAVES         (SLAVES                 ),
    .SELECTOR_TYPE  (PZBCM_SELECTOR_ONEHOT  )
  ) u_mux (
    .i_command_select     (command_grand          ),
    .i_write_data_select  (data_grant             ),
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
        response_select <= command_grand;
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
      .DATA_DEPTH     (DATA_DEPTH     ),
      .SVA_CHECKER    (0              )
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
      .DATA_VALID     (MASTER_FIFO    ),
      .SVA_CHECKER    (0              )
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
