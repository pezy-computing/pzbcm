//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_command_counter
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG      = '0,
  parameter int               WIDTH           = 8,
  parameter bit [7:0]         TARGET_COMMAND  = '1
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
      is_target_command(corebus_if.mcmd);
  end

  function automatic logic is_target_command(
    pzcorebus_command_type  mcmd
  );
    case (mcmd)
      PZCOREBUS_READ:               return TARGET_COMMAND[0];
      PZCOREBUS_WRITE:              return TARGET_COMMAND[1];
      PZCOREBUS_WRITE_NON_POSTED:   return TARGET_COMMAND[2];
      PZCOREBUS_BROADCAST:          return TARGET_COMMAND[3];
      PZCOREBUS_ATOMIC:             return TARGET_COMMAND[4];
      PZCOREBUS_ATOMIC_NON_POSTED:  return TARGET_COMMAND[5];
      PZCOREBUS_MESSAGE:            return TARGET_COMMAND[6];
      PZCOREBUS_MESSAGE_NON_POSTED: return TARGET_COMMAND[7];
      default:                      return '0;
    endcase
  endfunction
endmodule
