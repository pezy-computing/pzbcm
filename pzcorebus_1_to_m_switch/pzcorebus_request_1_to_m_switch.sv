//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_request_1_to_m_switch
  import  pzcorebus_pkg::*,
          pzbcm_selector_pkg::*;
#(
  parameter pzcorebus_config    BUS_CONFIG        = '0,
  parameter int                 MASTERS           = 2,
  parameter bit                 EXTERNAL_DECODE   = 0,
  parameter pzbcm_selector_type SELECTOR_TYPE     = PZBCM_SELECTOR_BINARY,
  parameter int                 SELECT_WIDTH      = calc_select_width(SELECTOR_TYPE, MASTERS),
  parameter int                 SELECT_LSB        = BUS_CONFIG.address_width - SELECT_WIDTH,
  parameter bit                 WAIT_FOR_DATA     = 0,
  parameter bit                 ENABLE_BROADCAST  = 0,
  parameter bit                 SLAVE_FIFO        = 0,
  parameter bit                 MASTER_FIFO       = 0,
  parameter int                 COMMAND_DEPTH     = 2,
  parameter int                 DATA_DEPTH        = 2,
  parameter bit                 ALIGN_OUT         = 0,
  parameter int                 MINFO_WIDTH       = get_request_info_width(BUS_CONFIG, 1)
)(
  input   var                                 i_clk,
  input   var                                 i_rst_n,
  output  var pzcorebus_command_type          o_mcmd,
  output  var [BUS_CONFIG.id_width-1:0]       o_mid,
  output  var [BUS_CONFIG.address_width-1:0]  o_maddr,
  output  var [MINFO_WIDTH-1:0]               o_minfo,
  input   var [SELECT_WIDTH-1:0]              i_select,
  interface.request_slave                     slave_if,
  interface.request_master                    master_if[MASTERS]
);
  localparam  bit BROADCAST = (BUS_CONFIG.profile == PZCOREBUS_CSR) && ENABLE_BROADCAST;

  pzcorebus_request_if #(BUS_CONFIG)  aligner_if();
  pzcorebus_request_if #(BUS_CONFIG)  switch_if[MASTERS]();

//--------------------------------------------------------------
//  Slave Command/Data Alignment
//--------------------------------------------------------------
  if (BUS_CONFIG.profile != PZCOREBUS_CSR) begin : g_slave_aligner
    pzcorebus_command_data_aligner_core #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .WAIT_FOR_DATA  (WAIT_FOR_DATA  ),
      .RELAX_MODE     (1              ),
      .SLAVE_FIFO     (SLAVE_FIFO     ),
      .COMMAND_DEPTH  (COMMAND_DEPTH  ),
      .DATA_DEPTH     (DATA_DEPTH     )
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
      .DATA_VALID     (SLAVE_FIFO     )
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
      o_mcmd  = aligner_if.mcmd;
      o_mid   = aligner_if.mid;
      o_maddr = aligner_if.maddr;
      o_minfo = aligner_if.minfo;
    end

    always_comb begin
      select_in = i_select;
    end
  end
  else begin : g_command_select
    always_comb begin
      o_mcmd  = pzcorebus_command_type'(0);
      o_mid   = '0;
      o_maddr = '0;
      o_minfo = '0;
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

  if (BUS_CONFIG.profile != PZCOREBUS_CSR) begin : g_data_select
    logic [MASTERS-1:0] select_latched;

    always_comb begin
      if (aligner_if.mcmd_valid) begin
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
      else if (aligner_if.command_ack()) begin
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
    logic command_active;
    logic command_done;
    logic data_active;

    always_comb begin
      if (!command_done) begin
        command_active  =
          command_select[i] ||
          (BROADCAST && (aligner_if.mcmd == PZCOREBUS_BROADCAST));
      end
      else begin
        command_active  = '0;
      end
      data_active = data_select[i];

      switch_if[i].mcmd_valid   = (command_active) ? mcmd_valid                : '0;
      scmd_accept[i]            = (command_active) ? switch_if[i].scmd_accept  : '1;
      switch_if[i].mdata_valid  = (data_active   ) ? mdata_valid               : '0;
      sdata_accept[i]           = (data_active   ) ? switch_if[i].sdata_accept : '0;
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

//--------------------------------------------------------------
//  Master Command/Data Alignment
//--------------------------------------------------------------
  for (genvar i = 0;i < MASTERS;++i) begin : g_master_aligner
    if ((BUS_CONFIG.profile != PZCOREBUS_CSR) && ALIGN_OUT && MASTER_FIFO) begin : g
      pzcorebus_command_data_aligner #(
        .BUS_CONFIG     (BUS_CONFIG     ),
        .RELAX_MODE     (1              ),
        .SLAVE_FIFO     (1              ),
        .COMMAND_DEPTH  (COMMAND_DEPTH  ),
        .DATA_DEPTH     (DATA_DEPTH     )
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
        .DATA_VALID     (MASTER_FIFO    )
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
