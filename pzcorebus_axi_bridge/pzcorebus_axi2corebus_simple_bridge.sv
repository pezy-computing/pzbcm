//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_axi2corebus_simple_bridge
  import  pzcorebus_pkg::*,
          pzaxi_pkg::*,
          pzbcm_arbiter_pkg::*;
#(
  parameter pzaxi_config      AXI_CONFIG            = '0,
  parameter pzcorebus_config  COREBUS_CONFIG        = '0,
  parameter int               COMMAND_FIFO_DEPTH    = 2,
  parameter int               WRITE_DATA_FIFO_DEPTH = 2,
  parameter int               RESPONSE_FIFO_DEPTH   = 0,
  parameter int               BID_FIFO_DEPTH        = 8,
  parameter bit               SUPPORT_4BYTES_ACCESS = 0
)(
  input var           i_clk,
  input var           i_rst_n,
  pzaxi_if.slave      axi_if,
  pzcorebus_if.master corebus_if
);
  `include  "pzcorebus_macros.svh"

  localparam  int UNIT_WIDTH  = 32;

  initial begin
    if (is_memory_h_profile(COREBUS_CONFIG)) begin
      assume (COREBUS_CONFIG.unit_data_width == UNIT_WIDTH);
    end
  end

  localparam  int ADDRESS_WIDTH         = COREBUS_CONFIG.address_width;
  localparam  int LENGTH_WIDTH          = get_length_width(COREBUS_CONFIG, 1);
  localparam  int UNPACKED_LENGTH_WIDTH = get_unpacked_length_width(COREBUS_CONFIG);
  localparam  int OFFSET_LSB            = $clog2(UNIT_WIDTH / 8);
  localparam  int OFFSET_WIDTH          = $clog2(COREBUS_CONFIG.data_width / UNIT_WIDTH);
  localparam  int BVALID_COUNT_WIDTH    = $clog2(BID_FIFO_DEPTH + 1);
  localparam  int AXI_ADDRESS_WIDTH     = AXI_CONFIG.address_width;

  function automatic logic is_4bytes_access(
    pzaxi_burst_length                  axlen,
    logic [$bits(pzaxi_burst_size)-1:0] axsize
  );
    return
      SUPPORT_4BYTES_ACCESS &&
      (axlen == pzaxi_burst_length'(0)) && (axsize == PZAXI_4_BYTES_BURST);
  endfunction

  function automatic logic [ADDRESS_WIDTH-1:0] get_maddr(
    logic [AXI_ADDRESS_WIDTH-1:0]       axaddr,
    pzaxi_burst_length                  axlen,
    logic [$bits(pzaxi_burst_size)-1:0] axsize
  );
    if (is_4bytes_access(axlen, axsize)) begin
      return ADDRESS_WIDTH'({axaddr[AXI_ADDRESS_WIDTH-1:2], 2'b01});
    end
    else begin
      return ADDRESS_WIDTH'({axaddr[AXI_ADDRESS_WIDTH-1:2], 2'b00});
    end
  endfunction

  function automatic logic [LENGTH_WIDTH-1:0] get_mlength(
    logic [AXI_ADDRESS_WIDTH-1:0]       axaddr,
    pzaxi_burst_length                  axlen,
    logic [$bits(pzaxi_burst_size)-1:0] axsize
  );
    pzaxi_burst_length_unpacked       burst_length;
    logic [UNPACKED_LENGTH_WIDTH-1:0] length;
    logic [UNPACKED_LENGTH_WIDTH-1:0] offset;

    burst_length  = pzaxi_burst_length_unpacked'(axlen) + pzaxi_burst_length_unpacked'(1);
    if (`pzcorebus_memoy_l_profile(COREBUS_CONFIG)) begin
      return LENGTH_WIDTH'(burst_length);
    end
    else if (is_4bytes_access(axlen, axsize)) begin
      return LENGTH_WIDTH'(1);
    end
    else begin
      length  = UNPACKED_LENGTH_WIDTH'({burst_length, OFFSET_WIDTH'(0)});
      offset  = UNPACKED_LENGTH_WIDTH'(axaddr[OFFSET_LSB+:OFFSET_WIDTH]);
      return LENGTH_WIDTH'(length - offset);
    end
  endfunction

  pzcorebus_if #(COREBUS_CONFIG)  read_bus_if();
  pzcorebus_if #(COREBUS_CONFIG)  write_bus_if();
  pzcorebus_if #(COREBUS_CONFIG)  switch_if[2]();

//--------------------------------------------------------------
//  Read channel
//--------------------------------------------------------------
  always_comb begin
    axi_if.arready          = read_bus_if.scmd_accept;
    read_bus_if.mcmd_valid  = axi_if.arvalid;
    read_bus_if.mcmd        = PZCOREBUS_READ;
    read_bus_if.mid         = axi_if.arid;
    read_bus_if.maddr       = get_maddr(axi_if.araddr, axi_if.arlen, axi_if.arsize);
    read_bus_if.mlength     = get_mlength(axi_if.araddr, axi_if.arlen, axi_if.arsize);
    read_bus_if.minfo       = '0;
  end

  always_comb begin
    read_bus_if.mdata_valid   = '0;
    read_bus_if.mdata         = '0;
    read_bus_if.mdata_byteen  = '0;
    read_bus_if.mdata_last    = '0;
  end

  always_comb begin
    read_bus_if.mresp_accept  = axi_if.rready;
    axi_if.rvalid             = read_bus_if.sresp_valid;
    axi_if.rid                = read_bus_if.sid;
    axi_if.rresp              = (read_bus_if.serror) ? PZAXI_SLVERR : PZAXI_OKAY;
    axi_if.rdata              = read_bus_if.sdata;
    axi_if.rlast              = read_bus_if.sresp_last[0];
    axi_if.ruser              = '0;
  end

  pzcorebus_fifo #(
    .BUS_CONFIG     (COREBUS_CONFIG       ),
    .COMMAND_DEPTH  (COMMAND_FIFO_DEPTH   ),
    .DATA_DEPTH     (0                    ),
    .RESPONSE_DEPTH (RESPONSE_FIFO_DEPTH  )
  ) u_read_fifo (
    .i_clk          (i_clk        ),
    .i_rst_n        (i_rst_n      ),
    .i_clear        ('0           ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (read_bus_if  ),
    .master_if      (switch_if[0] )
  );

//--------------------------------------------------------------
//  Write channel
//--------------------------------------------------------------
  logic                           bid_empty;
  logic                           bid_full;
  logic                           bid_push;
  logic                           bid_pop;
  logic [AXI_CONFIG.id_width-1:0] bid;
  logic [BVALID_COUNT_WIDTH-1:0]  bvalid_count;
  logic [1:0]                     bvalid_count_up_down;
  logic                           bvalid_count_empty;
  logic                           bvalid_count_full;

  always_comb begin
    bid_push  = axi_if.awvalid && axi_if.awready;
    bid_pop   = axi_if.bvalid  && axi_if.bready;
  end

  pzbcm_fifo #(
    .WIDTH  (AXI_CONFIG.id_width  ),
    .DEPTH  (BID_FIFO_DEPTH       )
  ) u_bid_fifo (
    .i_clk          (i_clk        ),
    .i_rst_n        (i_rst_n      ),
    .i_clear        ('0           ),
    .o_empty        (bid_empty    ),
    .o_almost_full  (),
    .o_full         (bid_full     ),
    .o_word_count   (),
    .i_push         (bid_push     ),
    .i_data         (axi_if.awid  ),
    .i_pop          (bid_pop      ),
    .o_data         (bid          )
  );

  always_comb begin
    bvalid_count_up_down[1] = axi_if.wvalid && axi_if.wready && axi_if.wlast;
    bvalid_count_up_down[0] = axi_if.bvalid && axi_if.bready;
    bvalid_count_empty      = bvalid_count == BVALID_COUNT_WIDTH'(0);
    bvalid_count_full       = bvalid_count == BVALID_COUNT_WIDTH'(BID_FIFO_DEPTH);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      bvalid_count  <= BVALID_COUNT_WIDTH'(0);
    end
    else if (bvalid_count_up_down == 2'b10) begin
      bvalid_count  <= bvalid_count + BVALID_COUNT_WIDTH'(1);
    end
    else if (bvalid_count_up_down == 2'b01) begin
      bvalid_count  <= bvalid_count - BVALID_COUNT_WIDTH'(1);
    end
  end

  always_comb begin
    axi_if.awready          = (!bid_full) && write_bus_if.scmd_accept;
    write_bus_if.mcmd_valid = (!bid_full) && axi_if.awvalid;
    write_bus_if.mcmd       = PZCOREBUS_WRITE;
    write_bus_if.mid        = axi_if.awid;
    write_bus_if.maddr      = get_maddr(axi_if.awaddr, axi_if.awlen, axi_if.awsize);
    write_bus_if.mlength    = get_mlength(axi_if.awaddr, axi_if.awlen, axi_if.awsize);
    write_bus_if.minfo      = '0;
  end

  always_comb begin
    axi_if.wready             = (!bvalid_count_full) && write_bus_if.sdata_accept;
    write_bus_if.mdata_valid  = (!bvalid_count_full) && axi_if.wvalid;
    write_bus_if.mdata        = axi_if.wdata;
    write_bus_if.mdata_byteen = axi_if.wstrb;
    write_bus_if.mdata_last   = axi_if.wlast;
  end

  always_comb begin
    write_bus_if.mresp_accept = '1;
    axi_if.bvalid             = (!bvalid_count_empty) && (!bid_empty);
    axi_if.bid                = bid;
    axi_if.bresp              = PZAXI_OKAY;
    axi_if.buser              = '0;
  end

  pzcorebus_fifo #(
    .BUS_CONFIG     (COREBUS_CONFIG         ),
    .COMMAND_DEPTH  (COMMAND_FIFO_DEPTH     ),
    .DATA_DEPTH     (WRITE_DATA_FIFO_DEPTH  ),
    .RESPONSE_DEPTH (0                      )
  ) u_write_fifo (
    .i_clk          (i_clk        ),
    .i_rst_n        (i_rst_n      ),
    .i_clear        ('0           ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (write_bus_if ),
    .master_if      (switch_if[1] )
  );

//--------------------------------------------------------------
//  Switch
//--------------------------------------------------------------
  pzcorebus_m_to_1_switch #(
    .BUS_CONFIG       (COREBUS_CONFIG ),
    .SLAVES           (2              ),
    .EXTERNAL_DECODE  (1              ),
    .ENABLE_ARBITER   (2'b01          )
  ) u_switch (
    .i_clk            (i_clk                            ),
    .i_rst_n          (i_rst_n                          ),
    .i_arbiter_config (PZBCM_ARBITER_CONFIG_ROUND_ROBIN ),
    .o_sid            (),
    .i_select         (1'd0                             ),
    .slave_if         (switch_if                        ),
    .master_if        (corebus_if                       )
  );
endmodule
