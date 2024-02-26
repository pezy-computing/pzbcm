//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_csrbus_upsizer
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  SLAVE_CONFIG          = '0,
  parameter pzcorebus_config  MASTER_CONFIG         = '0,
  parameter bit [1:0]         SLAVE_SLICER          = '0,
  parameter bit [1:0]         MASTER_SLICER         = '0,
  parameter bit               SVA_CHECKER           = 1,
  parameter bit               REQUEST_SVA_CHECKER   = SVA_CHECKER,
  parameter bit               RESPONSE_SVA_CHECKER  = SVA_CHECKER
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if,
  pzcorebus_if.master master_if
);
  initial begin
    assume (is_csr_profile(SLAVE_CONFIG));
    assume (is_csr_profile(MASTER_CONFIG));
    assume (MASTER_CONFIG.data_width > SLAVE_CONFIG.data_width);
    assume ((MASTER_CONFIG.data_width % SLAVE_CONFIG.data_width) == 0);
    assume (MASTER_CONFIG.use_byte_enable);
  end

  localparam  int WORD_INDEX_WIDTH          = $clog2(MASTER_CONFIG.data_width / SLAVE_CONFIG.data_width);
  localparam  int WORD_INDEX_LSB            = $clog2(SLAVE_CONFIG.data_width / 8);
  localparam  int SLAVE_BYTE_ENABLE_WIDTH   = get_byte_enable_width(SLAVE_CONFIG, 1);
  localparam  int SLAVE_BYTE_SIZE           = SLAVE_CONFIG.data_width / 8;
  localparam  int MASTER_BYTE_ENABLE_WIDTH  = get_byte_enable_width(MASTER_CONFIG, 1);

  logic [1:0][WORD_INDEX_WIDTH-1:0] word_index;
  logic                             wait_fo_response;
  pzcorebus_if #(SLAVE_CONFIG)      slicer_if();
  pzcorebus_if #(MASTER_CONFIG)     upsizer_if();

//--------------------------------------------------------------
//  Slave Slicer
//--------------------------------------------------------------
  pzcorebus_slicer #(
    .BUS_CONFIG           (SLAVE_CONFIG         ),
    .REQUEST_VALID        (SLAVE_SLICER[0]      ),
    .RESPONSE_VALID       (SLAVE_SLICER[1]      ),
    .REQUEST_SVA_CHECKER  (REQUEST_SVA_CHECKER  ),
    .RESPONSE_SVA_CHECKER ('0                   )
  ) u_slave_slicer (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (slave_if   ),
    .master_if  (slicer_if  )
  );

//--------------------------------------------------------------
//  Upsizee
//--------------------------------------------------------------
  always_comb begin
    if (wait_fo_response) begin
      word_index[0] = word_index[1];
    end
    else begin
      word_index[0] = slicer_if.maddr[WORD_INDEX_LSB+:WORD_INDEX_WIDTH];
    end
  end

  always_ff @(posedge i_clk) begin
    if (slicer_if.command_non_posted_ack()) begin
      word_index[1] <= word_index[0];
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      wait_fo_response  <= '0;
    end
    else if (slicer_if.response_last_ack()) begin
      wait_fo_response  <= '0;
    end
    else if (slicer_if.command_non_posted_ack()) begin
      wait_fo_response  <= '1;
    end
  end

  always_comb begin
    slicer_if.scmd_accept   = (!wait_fo_response) && upsizer_if.scmd_accept;
    upsizer_if.mcmd_valid   = (!wait_fo_response) && slicer_if.mcmd_valid;
    upsizer_if.mcmd         = slicer_if.mcmd;
    upsizer_if.mid          = slicer_if.mid;
    upsizer_if.maddr        = slicer_if.maddr;
    upsizer_if.minfo        = slicer_if.minfo;
    upsizer_if.mdata        = get_mdata(slicer_if.mdata);
    upsizer_if.mdata_byteen = get_mdata_byteen(word_index[0], slicer_if.mdata_byteen);
  end

  always_comb begin
    upsizer_if.mlength      = '0;
    upsizer_if.mdata_valid  = '0;
    upsizer_if.mdata_last   = '0;
  end

  always_comb begin
    upsizer_if.mresp_accept = wait_fo_response && slicer_if.mresp_accept;
    slicer_if.sresp_valid   = wait_fo_response && upsizer_if.sresp_valid;
    slicer_if.sresp         = upsizer_if.sresp;
    slicer_if.sid           = upsizer_if.sid;
    slicer_if.serror        = upsizer_if.serror;
    slicer_if.sinfo         = upsizer_if.sinfo;
    slicer_if.sdata         = get_sdata(word_index[0], upsizer_if.sdata);
  end

  always_comb begin
    slicer_if.sresp_uniten  = '0;
    slicer_if.sresp_last    = '0;
  end

  function automatic logic [MASTER_CONFIG.data_width-1:0] get_mdata(
    logic [SLAVE_CONFIG.data_width-1:0] slave_mdata
  );
    return {(MASTER_CONFIG.data_width/SLAVE_CONFIG.data_width){slave_mdata}};
  endfunction

  function automatic logic [MASTER_BYTE_ENABLE_WIDTH-1:0] get_mdata_byteen(
    logic [WORD_INDEX_WIDTH-1:0]        word_index,
    logic [SLAVE_BYTE_ENABLE_WIDTH-1:0] slave_mdata_byteen
  );
    logic [MASTER_BYTE_ENABLE_WIDTH-1:0]  master_mdata_byteen;

    master_mdata_byteen = '0;
    if (SLAVE_CONFIG.use_byte_enable) begin
      master_mdata_byteen[SLAVE_BYTE_SIZE*word_index+:SLAVE_BYTE_SIZE]  = SLAVE_BYTE_SIZE'(slave_mdata_byteen);
    end
    else begin
      master_mdata_byteen[SLAVE_BYTE_SIZE*word_index+:SLAVE_BYTE_SIZE]  = '1;
    end

    return master_mdata_byteen;
  endfunction

  function automatic logic [SLAVE_CONFIG.data_width-1:0] get_sdata(
    logic [WORD_INDEX_WIDTH-1:0]          word_index,
    logic [MASTER_CONFIG.data_width-1:0]  master_sdata
  );
    return master_sdata[SLAVE_CONFIG.data_width*word_index+:SLAVE_CONFIG.data_width];
  endfunction

//--------------------------------------------------------------
//  Master Slicer
//--------------------------------------------------------------
  pzcorebus_slicer #(
    .BUS_CONFIG           (MASTER_CONFIG        ),
    .REQUEST_VALID        (MASTER_SLICER[0]     ),
    .RESPONSE_VALID       (MASTER_SLICER[1]     ),
    .REQUEST_SVA_CHECKER  ('0                   ),
    .RESPONSE_SVA_CHECKER (RESPONSE_SVA_CHECKER )
  ) u_master_slicer (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (upsizer_if ),
    .master_if  (master_if  )
  );
endmodule
