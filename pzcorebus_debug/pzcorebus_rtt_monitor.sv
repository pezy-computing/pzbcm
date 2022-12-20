//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_rtt_monitor
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG  = '0,
  parameter   int               RTT_WIDTH   = 24,
  parameter   int               RTT_ENTRIES = 4,
  localparam  type              RTT         = logic [RTT_WIDTH-1:0]
)(
  input   var                       i_clk,
  input   var                       i_rst_n,
  input   var                       i_enable,
  input   var                       i_clear,
  pzcorebus_if.monitor              corebus_if,
  output  var RTT [RTT_ENTRIES-1:0] o_rtt_worst,
  output  var RTT [RTT_ENTRIES-1:0] o_rtt_best
);
  typedef logic [BUS_CONFIG.id_width-1:0] pzcorebus_id;

  typedef struct packed {
    logic         busy;
    pzcorebus_id  id;
  } pzcorebus_rtt_monitor_state;

  logic [RTT_ENTRIES-1:0]                       ready;
  pzcorebus_rtt_monitor_state [RTT_ENTRIES-1:0] state;

  always_comb begin
    ready = get_ready(state, corebus_if.mid);
  end

  function automatic logic [RTT_ENTRIES-1:0] get_ready(
    pzcorebus_rtt_monitor_state [RTT_ENTRIES-1:0] state,
    pzcorebus_id                                  mid
  );
    logic [RTT_ENTRIES-1:0] id_match;
    logic [RTT_ENTRIES-1:0] active_entry;

    for (int i = 0;i < RTT_ENTRIES;++i) begin
      id_match[i] = state[i].busy && (mid == state[i].id);
      if (i == 0) begin
        active_entry[i] = !state[i].busy;
      end
      else begin
        active_entry[i] = (!state[i].busy) && state[i-1].busy;
      end
    end

    return (id_match == '0) ? active_entry : '0;
  endfunction

  for (genvar i = 0;i < RTT_ENTRIES;++i) begin : g_rtt
    logic start_tracking;
    logic finish_tracking;
    RTT   rtt;
    RTT   rtt_worst;
    RTT   rtt_best;

    always_comb begin
      o_rtt_worst[i]  = rtt_worst;
      o_rtt_best[i]   = rtt_best;
    end

    always_comb begin
      start_tracking  =
        corebus_if.command_non_posted_ack() && ready[i];
      finish_tracking =
        corebus_if.response_last_ack() &&
        state[i].busy && (corebus_if.sid == state[i].id);
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        state[i].busy <= '0;
      end
      else if ((!i_enable) || finish_tracking) begin
        state[i].busy <= '0;
      end
      else if (start_tracking) begin
        state[i].busy <= '1;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        state[i].id <= '0;
      end
      else if (i_enable && start_tracking) begin
        state[i].id <= corebus_if.mid;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        rtt <= '0;
      end
      else if ((!i_enable) || finish_tracking) begin
        rtt <= '0;
      end
      else if (state[i].busy) begin
        rtt <= rtt + RTT'(1);;
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        rtt_worst <= '0;
        rtt_best  <= '1;
      end
      else if (i_clear) begin
        rtt_worst <= '0;
        rtt_best  <= '1;
      end
      else if (i_enable && finish_tracking) begin
        if (rtt > rtt_worst) begin
          rtt_worst <= rtt;
        end
        if (rtt < rtt_best) begin
          rtt_best  <= rtt;
        end
      end
    end
  end
endmodule
