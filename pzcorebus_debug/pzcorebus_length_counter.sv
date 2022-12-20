//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_length_counter
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG      = '0,
  parameter int               WIDTH           = 16,
  parameter bit [7:0]         TARGET_COMMAND  = '1,
  parameter bit               BURST_COUNT     = 0
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

  pzcorebus_utils #(BUS_CONFIG) u_utils();

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
    if ((BUS_CONFIG.profile == PZCOREBUS_MEMORY_H) && BURST_COUNT) begin
      length  = WIDTH'(
        u_utils.get_burst_length(corebus_if.mcmd, corebus_if.maddr, corebus_if.mlength)
      );
    end
    else begin
      length  = WIDTH'(
        u_utils.unpack_length(corebus_if.mlength)
      );
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
      default:                      return '0;
    endcase
  endfunction
endmodule
