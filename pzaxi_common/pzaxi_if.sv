//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
interface pzaxi_if
  import  pzaxi_pkg::*;
#(
  parameter pzaxi_config  BUS_CONFIG  = '0
);
  localparam  AWUSER_WIDTH  = get_awuser_width(BUS_CONFIG, 1);
  localparam  WUSER_WIDTH   = get_wuser_width(BUS_CONFIG, 1);
  localparam  BUSER_WIDTH   = get_buser_width(BUS_CONFIG, 1);
  localparam  ARUSER_WIDTH  = get_aruser_width(BUS_CONFIG, 1);
  localparam  RUSER_WIDTH   = get_ruser_width(BUS_CONFIG, 1);

  logic                                     awready;
  logic                                     awvalid;
  logic [BUS_CONFIG.id_width-1:0]           awid;
  logic [BUS_CONFIG.address_width-1:0]      awaddr;
  pzaxi_burst_length                        awlen;
  logic [$bits(pzaxi_burst_size)-1:0]       awsize;
  logic [$bits(pzaxi_burst_type)-1:0]       awburst;
  pzaxi_write_cache                         awcache;
  pzaxi_permission                          awprot;
  logic [$bits(pzaxi_lock)-1:0]             awlock;
  pzaxi_qos                                 awqos;
  logic [AWUSER_WIDTH-1:0]                  awuser;
  logic                                     wready;
  logic                                     wvalid;
  logic [BUS_CONFIG.data_width-1:0]         wdata;
  logic [BUS_CONFIG.data_width/8-1:0]       wstrb;
  logic                                     wlast;
  logic [WUSER_WIDTH-1:0]                   wuser;
  logic                                     bready;
  logic                                     bvalid;
  logic [BUS_CONFIG.id_width-1:0]           bid;
  logic [$bits(pzaxi_response_status)-1:0]  bresp;
  logic [BUSER_WIDTH-1:0]                   buser;
  logic                                     arready;
  logic                                     arvalid;
  logic [BUS_CONFIG.id_width-1:0]           arid;
  logic [BUS_CONFIG.address_width-1:0]      araddr;
  pzaxi_burst_length                        arlen;
  logic [$bits(pzaxi_burst_size)-1:0]       arsize;
  logic [$bits(pzaxi_burst_type)-1:0]       arburst;
  pzaxi_write_cache                         arcache;
  pzaxi_permission                          arprot;
  logic [$bits(pzaxi_lock)-1:0]             arlock;
  pzaxi_qos                                 arqos;
  logic [AWUSER_WIDTH-1:0]                  aruser;
  logic                                     rready;
  logic                                     rvalid;
  logic [BUS_CONFIG.id_width-1:0]           rid;
  logic [$bits(pzaxi_response_status)-1:0]  rresp;
  logic [BUS_CONFIG.data_width-1:0]         rdata;
  logic                                     rlast;
  logic [RUSER_WIDTH-1:0]                   ruser;

  modport master (
    input   awready,
    output  awvalid,
    output  awid,
    output  awaddr,
    output  awlen,
    output  awsize,
    output  awburst,
    output  awcache,
    output  awprot,
    output  awlock,
    output  awqos,
    output  awuser,
    input   wready,
    output  wvalid,
    output  wdata,
    output  wstrb,
    output  wlast,
    output  wuser,
    output  bready,
    input   bvalid,
    input   bid,
    input   bresp,
    input   buser,
    input   arready,
    output  arvalid,
    output  arid,
    output  araddr,
    output  arlen,
    output  arsize,
    output  arburst,
    output  arcache,
    output  arprot,
    output  arlock,
    output  arqos,
    output  aruser,
    output  rready,
    input   rvalid,
    input   rid,
    input   rresp,
    input   rdata,
    input   rlast,
    input   ruser
  );

  modport slave (
    output  awready,
    input   awvalid,
    input   awid,
    input   awaddr,
    input   awlen,
    input   awsize,
    input   awburst,
    input   awcache,
    input   awprot,
    input   awlock,
    input   awqos,
    input   awuser,
    output  wready,
    input   wvalid,
    input   wdata,
    input   wstrb,
    input   wlast,
    input   wuser,
    input   bready,
    output  bvalid,
    output  bid,
    output  bresp,
    output  buser,
    output  arready,
    input   arvalid,
    input   arid,
    input   araddr,
    input   arlen,
    input   arsize,
    input   arburst,
    input   arcache,
    input   arprot,
    input   arlock,
    input   arqos,
    input   aruser,
    input   rready,
    output  rvalid,
    output  rid,
    output  rresp,
    output  rdata,
    output  rlast,
    output  ruser
  );

  modport monitor (
    input awready,
    input awvalid,
    input awid,
    input awaddr,
    input awlen,
    input awsize,
    input awburst,
    input awcache,
    input awprot,
    input awlock,
    input awqos,
    input awuser,
    input wready,
    input wvalid,
    input wdata,
    input wstrb,
    input wlast,
    input wuser,
    input bready,
    input bvalid,
    input bid,
    input bresp,
    input buser,
    input arready,
    input arvalid,
    input arid,
    input araddr,
    input arlen,
    input arsize,
    input arburst,
    input arcache,
    input arprot,
    input arlock,
    input arqos,
    input aruser,
    input rready,
    input rvalid,
    input rid,
    input rresp,
    input rdata,
    input rlast,
    input ruser
  );
endinterface
