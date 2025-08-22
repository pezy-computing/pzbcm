//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_packer_data_fifo
  import  pzcorebus_pkg::*,
          pzbcm_sram_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG  = '0,
  parameter pzbcm_sram_params SRAM_PARAMS = '0,
  parameter type              SRAM_CONFIG = logic
)(
  input   var                     i_clk,
  input   var                     i_rst_n,
  input   var                     i_clear,
  output  var                     o_fifo_empty,
  output  var                     o_fifo_full,
  input   var SRAM_CONFIG         i_sram_config,
  pzcorebus_if.write_data_slave   slave_if,
  pzcorebus_if.write_data_master  master_if
);
  localparam  int WIDTH = get_packed_write_data_width(BUS_CONFIG, 1);

  logic             full;
  logic             empty;
  logic             push;
  logic [WIDTH-1:0] push_data;
  logic             pop;
  logic [WIDTH-1:0] pop_data;

  always_comb begin
    slave_if.sdata_accept = !full;
    push                  = slave_if.mdata_valid;
    push_data             = slave_if.get_packed_write_data();
  end

  always_comb begin
    pop                   = master_if.sdata_accept;
    master_if.mdata_valid = !empty;
    master_if.put_packed_write_data(pop_data);
  end

  pzbcm_sram_fifo #(
    .SRAM_PARAMS  (SRAM_PARAMS  ),
    .SRAM_CONFIG  (SRAM_CONFIG  )
  ) u_fifo (
    .i_clk              (i_clk          ),
    .i_rst_n            (i_rst_n        ),
    .i_clear            (i_clear        ),
    .i_sram_config      (i_sram_config  ),
    .o_empty            (empty          ),
    .o_completely_empty (o_fifo_empty   ),
    .o_almost_full      (),
    .o_full             (full           ),
    .o_completely_full  (o_fifo_full    ),
    .i_push             (push           ),
    .i_data             (push_data      ),
    .i_pop              (pop            ),
    .o_data             (pop_data       )
  );
endmodule
