//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_corebus2axi_simple_bridge
  import  pzcorebus_pkg::*,
          pzaxi_pkg::*;
#(
  parameter pzcorebus_config  COREBUS_CONFIG        = '0,
  parameter pzaxi_config      AXI_CONFIG            = '0,
  parameter int               MAX_WRITE_REQUESTS    = (2**16) - 1,
  parameter bit               SVA_CHECKER           = 1,
  parameter bit               REQUEST_SVA_CHECKER   = SVA_CHECKER,
  parameter bit               RESPONSE_SVA_CHECKER  = SVA_CHECKER
)(
  input var                   i_clk,
  input var                   i_rst_n,
  input var [1:0]             i_blocking_mode,
  input var pzaxi_write_cache i_awcache,
  input var pzaxi_permission  i_awprot,
  input var pzaxi_lock        i_awlock,
  input var pzaxi_qos         i_awqos,
  input var pzaxi_write_cache i_arcache,
  input var pzaxi_permission  i_arprot,
  input var pzaxi_lock        i_arlock,
  input var pzaxi_qos         i_arqos,
  pzcorebus_if.slave          corebus_if,
  pzaxi_if.master             axi_if
);
  typedef logic [get_burst_length_width(COREBUS_CONFIG)-1:0]  pzcorebus_burst_length;

  function automatic pzaxi_burst_length get_burst_length(pzcorebus_burst_length length);
    return encode_burst_length(pzaxi_burst_length_unpacked'(length));
  endfunction

  function automatic pzaxi_burst_size get_burst_size();
    case (COREBUS_CONFIG.data_width)
      8:        return PZAXI_1_BYTE_BURST;
      16:       return PZAXI_2_BYTES_BURST;
      32:       return PZAXI_4_BYTES_BURST;
      64:       return PZAXI_8_BYTES_BURST;
      128:      return PZAXI_16_BYTES_BURST;
      256:      return PZAXI_32_BYTES_BURST;
      512:      return PZAXI_64_BYTES_BURST;
      default:  return PZAXI_128_BYTES_BURST;
    endcase
  endfunction

  localparam  bit [1:0] NON_BLOCKING      = 2'h0;
  localparam  bit [1:0] RW_BLOCKING       = 2'h1;
  localparam  bit [1:0] R_BLOCKING        = 2'h2;
  localparam  int       WRITE_COUNT_WIDTH = $clog2(MAX_WRITE_REQUESTS + 1);

  logic [WRITE_COUNT_WIDTH-1:0] write_count;
  logic [1:0]                   write_count_up_down;
  logic [1:0]                   write_command_count;
  logic [1:0]                   write_command_count_up_down;
  logic                         write_command_count_full;
  logic                         write_busy;
  logic                         block_write;
  logic                         block_read;

  always_comb begin
    write_count_up_down[1]  = axi_if.awvalid && axi_if.awready;
    write_count_up_down[0]  = axi_if.bvalid  && axi_if.bready;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      write_count <= WRITE_COUNT_WIDTH'(0);
    end
    else if (write_count_up_down == 2'b10) begin
      write_count <= write_count + WRITE_COUNT_WIDTH'(1);
    end
    else if (write_count_up_down == 2'b01) begin
      write_count <= write_count - WRITE_COUNT_WIDTH'(1);
    end
  end

  always_comb begin
    write_command_count_up_down[1]  = axi_if.awvalid && axi_if.awready;
    write_command_count_up_down[0]  = axi_if.wvalid  && axi_if.wready && axi_if.wlast;
    write_command_count_full        = write_command_count == 2'(2);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      write_command_count <= 2'(0);
    end
    else if (write_command_count_up_down == 2'b10) begin
      write_command_count <= write_command_count + 2'(1);
    end
    else if (write_command_count_up_down == 2'b01) begin
      write_command_count <= write_command_count - 2'(1);
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      write_busy  <= '0;
    end
    else if (axi_if.awvalid && axi_if.awready) begin
      write_busy  <= '1;
    end
    else if (axi_if.bvalid && axi_if.bready) begin
      write_busy  <= '0;
    end
  end

  always_comb begin
    case (i_blocking_mode)
      RW_BLOCKING: begin
        block_write = write_command_count_full || write_busy;
        block_read  = write_busy;
      end
      R_BLOCKING: begin
        block_write = write_command_count_full;
        block_read  = write_count != WRITE_COUNT_WIDTH'(0);
      end
      default: begin
        block_write = write_command_count_full;
        block_read  = '0;
      end
    endcase
  end

  always_comb begin
    if (corebus_if.is_command_with_data()) begin
      corebus_if.scmd_accept  = (!block_write) && axi_if.awready;
      axi_if.awvalid          = (!block_write) && corebus_if.mcmd_valid;
      axi_if.arvalid          = '0;
    end
    else begin
      corebus_if.scmd_accept  = (!block_read) && axi_if.arready;
      axi_if.arvalid          = (!block_read) && corebus_if.mcmd_valid;
      axi_if.awvalid          = '0;
    end

    axi_if.awid     = corebus_if.mid;
    axi_if.awaddr   = (AXI_CONFIG.address_width)'(corebus_if.maddr);
    axi_if.awlen    = get_burst_length(corebus_if.get_burst_length());
    axi_if.awsize   = get_burst_size();
    axi_if.awburst  = PZAXI_INCR_BURST;
    axi_if.awcache  = i_awcache;
    axi_if.awprot   = i_awprot;
    axi_if.awlock   = i_awlock;
    axi_if.awqos    = i_awqos;
    axi_if.awuser   = '0;
    axi_if.arid     = corebus_if.mid;
    axi_if.araddr   = (AXI_CONFIG.address_width)'(corebus_if.maddr);
    axi_if.arlen    = encode_burst_length(pzaxi_burst_length_unpacked'(corebus_if.get_burst_length()));
    axi_if.arsize   = get_burst_size();
    axi_if.arburst  = PZAXI_INCR_BURST;
    axi_if.arcache  = i_arcache;
    axi_if.arprot   = i_arprot;
    axi_if.arlock   = i_arlock;
    axi_if.arqos    = i_arqos;
    axi_if.aruser   = '0;
  end

  always_comb begin
    if (axi_if.awvalid || (write_command_count > 2'(0))) begin
      corebus_if.sdata_accept = axi_if.wready;
      axi_if.wvalid           = corebus_if.mdata_valid;
    end
    else begin
      corebus_if.sdata_accept = '0;
      axi_if.wvalid           = '0;
    end

    axi_if.wdata  = corebus_if.mdata;
    axi_if.wstrb  = corebus_if.mdata_byteen;
    axi_if.wlast  = corebus_if.mdata_last;
    axi_if.wuser  = '0;
  end

  always_comb begin
    axi_if.bready           = '1;
    axi_if.rready           = corebus_if.mresp_accept;
    corebus_if.sresp_valid  = axi_if.rvalid;
    corebus_if.sid          = axi_if.rid;
    corebus_if.sresp        = PZCOREBUS_RESPONSE_WITH_DATA;
    corebus_if.serror       = axi_if.rresp inside {PZAXI_SLVERR, PZAXI_DECERR};
    corebus_if.sdata        = axi_if.rdata;
    corebus_if.sinfo        = '0;
    corebus_if.sresp_uniten = '1;
    corebus_if.sresp_last   = (axi_if.rlast) ? '1 : '0;
  end

//--------------------------------------------------------------
//  SVA checker
//--------------------------------------------------------------
  if (PZCOREBUS_ENABLE_SVA_CHECKER) begin : g_sva
    pzcorebus_sva_checker #(
      .BUS_CONFIG           (COREBUS_CONFIG       ),
      .REQUEST_SVA_CHECKER  (REQUEST_SVA_CHECKER  ),
      .RESPONSE_SVA_CHECKER (RESPONSE_SVA_CHECKER )
    ) u_sva_checker (
      .i_request_clk    (i_clk      ),
      .i_request_rst_n  (i_rst_n    ),
      .request_bus_if   (corebus_if ),
      .i_response_clk   (i_clk      ),
      .i_response_rst_n (i_rst_n    ),
      .response_bus_if  (corebus_if )
    );
  end
endmodule
