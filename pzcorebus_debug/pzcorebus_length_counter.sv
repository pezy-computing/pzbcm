//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_length_counter
  import  pzcorebus_pkg::*,
          pzcorebus_debug_pkg::*;
#(
  parameter pzcorebus_config                BUS_CONFIG      = '0,
  parameter int                             WIDTH           = 16,
  parameter pzcorebus_debug_target_command  TARGET_COMMAND  = '1,
  parameter bit                             BURST_COUNT     = 0
)(
  input var               i_clk,
  input var               i_rst_n,
  input var               i_enable,
  input var               i_clear,
  pzcorebus_if.monitor    corebus_if,
  output  var [WIDTH-1:0] o_count
);
  logic [WIDTH-1:0] count;
  logic [WIDTH-1:0] length;
  logic             hit_command;

  always_comb begin
    o_count = count;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      count <= '0;
    end
    else if (i_clear) begin
      count <= '0;
    end
    else if (i_enable && hit_command) begin
      count <= count + length;
    end
  end

  always_comb begin
    if (BURST_COUNT) begin
      length  = WIDTH'(corebus_if.get_burst_length());
    end
    else begin
      length  = WIDTH'(corebus_if.get_length());
    end
  end

  always_comb begin
    hit_command =
      corebus_if.command_ack() &&
      is_target_command(corebus_if.mcmd, TARGET_COMMAND);
  end
endmodule
