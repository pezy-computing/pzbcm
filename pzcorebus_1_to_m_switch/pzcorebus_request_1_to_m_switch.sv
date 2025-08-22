//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_request_1_to_m_switch
  import  pzcorebus_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config    BUS_CONFIG                  = '0,
  parameter int                 MASTERS                     = 2,
  parameter bit                 EXTERNAL_DECODE             = 0,
  parameter pzbcm_selector_type SELECTOR_TYPE               = PZBCM_SELECTOR_BINARY,
  parameter int                 SELECT_WIDTH                = calc_select_width(SELECTOR_TYPE, MASTERS),
  parameter int                 SELECT_LSB                  = BUS_CONFIG.address_width - SELECT_WIDTH,
  parameter bit                 WAIT_FOR_DATA               = 0,
  parameter bit                 WAIT_FOR_DATA_LAST          = 0,
  parameter bit                 ENABLE_BROADCAST            = 0,
  parameter bit                 ENABLE_BROADCAST_NON_POSTED = 0,
  parameter bit                 SLAVE_FIFO                  = 0,
  parameter bit                 MASTER_FIFO                 = 0,
  parameter int                 COMMAND_DEPTH               = 2,
  parameter int                 DATA_DEPTH                  = 2,
  parameter bit                 ALIGN_OUT                   = 0,
  parameter bit                 SVA_CHECKER                 = 1
)(
  input   var                     i_clk,
  input   var                     i_rst_n,
  output  var pzcorebus_command   o_mcmd,
  input   var [SELECT_WIDTH-1:0]  i_select,
  interface.request_slave         slave_if,
  interface.request_master        master_if[MASTERS]
);
  localparam  bit BROADCAST = is_csr_profile(BUS_CONFIG) && ENABLE_BROADCAST;

  pzcorebus_request_if #(BUS_CONFIG)  aligner_if();
  pzcorebus_request_if #(BUS_CONFIG)  switch_if[MASTERS]();

//--------------------------------------------------------------
//  Slave Command/Data Alignment
//--------------------------------------------------------------
  if (is_memory_profile(BUS_CONFIG)) begin : g_slave_aligner
    pzcorebus_command_data_aligner_core #(
      .BUS_CONFIG               (BUS_CONFIG           ),
      .WAIT_FOR_DATA            (WAIT_FOR_DATA        ),
      .RELAX_MODE               (1                    ),
      .THROUGH_NO_DATA_COMMAND  (!WAIT_FOR_DATA_LAST  ),
      .SLAVE_FIFO               (SLAVE_FIFO           ),
      .COMMAND_DEPTH            (COMMAND_DEPTH        ),
      .DATA_DEPTH               (DATA_DEPTH           ),
      .SVA_CHECKER              (SVA_CHECKER          )
    ) u_aligner (
      .i_clk        (i_clk      ),
      .i_rst_n      (i_rst_n    ),
      .o_mcmd_done  (),
      .o_mdata_done (),
      .o_mcmd       (),
      .o_mid        (),
      .o_maddr      (),
      .o_minfo      (),
      .slave_if     (slave_if   ),
      .master_if    (aligner_if )
    );
  end
  else begin : g_slave_aligner
    pzcorebus_request_fifo #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .COMMAND_DEPTH  (COMMAND_DEPTH  ),
      .COMMAND_VALID  (SLAVE_FIFO     ),
      .DATA_DEPTH     (DATA_DEPTH     ),
      .DATA_VALID     (SLAVE_FIFO     ),
      .SVA_CHECKER    (SVA_CHECKER    )
    ) u_fifo (
      .i_clk          (i_clk      ),
      .i_rst_n        (i_rst_n    ),
      .i_clear        ('0         ),
      .o_empty        (),
      .o_almost_full  (),
      .o_full         (),
      .slave_if       (slave_if   ),
      .master_if      (aligner_if )
    );
  end

//--------------------------------------------------------------
//  Switch
//--------------------------------------------------------------
  logic [SELECT_WIDTH-1:0]  select_in;
  logic [MASTERS-1:0]       command_select;
  logic [MASTERS-1:0]       data_select;

  if (EXTERNAL_DECODE) begin : g_command_select
    always_comb begin
      o_mcmd  = aligner_if.get_command();
    end

    always_comb begin
      select_in = i_select;
    end
  end
  else begin : g_command_select
    always_comb begin
      o_mcmd  = '0;
    end

    always_comb begin
      select_in = aligner_if.maddr[SELECT_LSB+:SELECT_WIDTH];
    end
  end

  if ((SELECTOR_TYPE == PZBCM_SELECTOR_BINARY) || (!EXTERNAL_DECODE)) begin : g_decoder
    always_comb begin
      for (int i = 0;i < MASTERS;++i) begin
        command_select[i] = select_in == SELECT_WIDTH'(i);
      end
    end
  end
  else begin : g_decoder
    always_comb begin
      command_select  = select_in;
    end
  end

  if (is_memory_profile(BUS_CONFIG)) begin : g_data_select
    logic [MASTERS-1:0] select_latched;

    always_comb begin
      if (aligner_if.command_with_data_valid()) begin
        data_select = command_select;
      end
      else begin
        data_select = select_latched;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        select_latched  <= '0;
      end
      else if (aligner_if.command_with_data_valid()) begin
        select_latched  <= command_select;
      end
    end
  end
  else begin : g_data_select
    always_comb begin
      data_select = '0;
    end
  end

  logic               mcmd_valid;
  logic [MASTERS-1:0] scmd_accept;
  logic               mdata_valid;
  logic [MASTERS-1:0] sdata_accept;

  always_comb begin
    mcmd_valid              = aligner_if.mcmd_valid;
    aligner_if.scmd_accept  = &scmd_accept;
    mdata_valid             = aligner_if.mdata_valid;
    aligner_if.sdata_accept = |sdata_accept;
  end

  for (genvar i = 0;i < MASTERS;++i) begin : g_request
    logic command_done;

    always_comb begin
      if (get_command_active(aligner_if.mcmd, command_select[i], command_done)) begin
        switch_if[i].mcmd_valid = mcmd_valid;
        scmd_accept[i]          = switch_if[i].scmd_accept;
      end
      else begin
        switch_if[i].mcmd_valid = '0;
        scmd_accept[i]          = '1;
      end

      if (data_select[i]) begin
        switch_if[i].mdata_valid  = mdata_valid;
        sdata_accept[i]           = switch_if[i].sdata_accept;
      end
      else begin
        switch_if[i].mdata_valid  = '0;
        sdata_accept[i]           = '0;
      end
      switch_if[i].put_request(aligner_if.get_request());
    end

    if (BROADCAST) begin : g
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          command_done  <= '0;
        end
        else if (aligner_if.command_ack()) begin
          command_done  <= '0;
        end
        else if (switch_if[i].command_ack()) begin
          command_done  <= '1;
        end
      end
    end
    else begin : g
      always_comb begin
        command_done  = '0;
      end
    end
  end

  function automatic logic get_command_active(
    pzcorebus_command_type  mcmd,
    logic                   command_select,
    logic                   command_done
  );
    if (BROADCAST) begin
      logic broadcast_command;

      if (ENABLE_BROADCAST_NON_POSTED) begin
        broadcast_command = pzcorebus_command_kind'(mcmd) == PZCOREBUS_BROADCAST_COMMAND;
      end
      else begin
        broadcast_command = mcmd == PZCOREBUS_BROADCAST;
      end

      return (!command_done) && (command_select || broadcast_command);
    end
    else begin
      return command_select;
    end
  endfunction

//--------------------------------------------------------------
//  Master Command/Data Alignment
//--------------------------------------------------------------
  for (genvar i = 0;i < MASTERS;++i) begin : g_master_aligner
    if (is_memory_profile(BUS_CONFIG) && ALIGN_OUT && MASTER_FIFO) begin : g
      pzcorebus_command_data_aligner_core #(
        .BUS_CONFIG     (BUS_CONFIG     ),
        .RELAX_MODE     (1              ),
        .SLAVE_FIFO     (1              ),
        .COMMAND_DEPTH  (COMMAND_DEPTH  ),
        .DATA_DEPTH     (DATA_DEPTH     ),
        .SVA_CHECKER    (0              )
      ) u_aligner (
        .i_clk      (i_clk        ),
        .i_rst_n    (i_rst_n      ),
        .slave_if   (switch_if[i] ),
        .master_if  (master_if[i] )
      );
    end
    else begin : g
      pzcorebus_request_fifo #(
        .BUS_CONFIG     (BUS_CONFIG     ),
        .COMMAND_DEPTH  (COMMAND_DEPTH  ),
        .COMMAND_VALID  (MASTER_FIFO    ),
        .DATA_DEPTH     (DATA_DEPTH     ),
        .DATA_VALID     (MASTER_FIFO    ),
        .SVA_CHECKER    (0              )
      ) u_fifo (
        .i_clk          (i_clk        ),
        .i_rst_n        (i_rst_n      ),
        .i_clear        ('0           ),
        .o_empty        (),
        .o_almost_full  (),
        .o_full         (),
        .slave_if       (switch_if[i] ),
        .master_if      (master_if[i] )
      );
    end
  end
endmodule
