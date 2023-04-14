//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_command_counter
  import  pzcorebus_pkg::*,
          pzcorebus_debug_pkg::*;
#(
  parameter pzcorebus_config                BUS_CONFIG      = '0,
  parameter int                             WIDTH           = 8,
  parameter pzcorebus_debug_target_command  TARGET_COMMAND  = '1
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_enable,
  input   var             i_clear,
  pzcorebus_if.monitor    corebus_if,
  output  var [WIDTH-1:0] o_count
);
  logic [WIDTH-1:0] count;
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
      count <= count + WIDTH'(1);
    end
  end

  always_comb begin
    hit_command =
      corebus_if.command_ack() &&
      is_target_command(corebus_if.mcmd, TARGET_COMMAND);
  end
endmodule
