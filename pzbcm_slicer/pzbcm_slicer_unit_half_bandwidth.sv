//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_slicer_unit_half_bandwidth #(
  parameter int WIDTH         = 1,
  parameter bit DISABLE_MBFF  = 0,
  parameter bit USE_RESET     = 1
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_valid,
  output  var             o_ready,
  input   var [WIDTH-1:0] i_data,
  output  var             o_valid,
  input   var             i_ready,
  output  var [WIDTH-1:0] o_data
);
  logic             valid;
  logic [WIDTH-1:0] data;

  always_comb begin
    o_ready = !valid;
  end

  always_comb begin
    o_valid = valid;
    o_data  = data;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      valid <= '0;
    end
    else if (!valid) begin
      valid <= i_valid;
    end
    else if (i_ready) begin
      valid <= '0;
    end
  end

  if (!DISABLE_MBFF) begin : g
    if (USE_RESET) begin : g
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          data  <= '0;
        end
        else if ((!valid) && i_valid) begin
          data  <= i_data;
        end
      end
    end
    else begin : g
      always_ff @(posedge i_clk) begin
        if ((!valid) && i_valid) begin
          data  <= i_data;
        end
      end
    end
  end
  else begin : g
    for (genvar i = 0;i < WIDTH;++i) begin : g
      logic d;

      always_comb begin
        data[i] = d;
      end

      if (USE_RESET) begin
        always_ff @(posedge i_clk, negedge i_rst_n) begin
          if (!i_rst_n) begin
            d <= '0;
          end
          else if ((!valid) && i_valid) begin
            d <= i_data[i];
          end
        end
      end
      else begin : g
        always_ff @(posedge i_clk) begin
          if ((!valid) && i_valid) begin
            d <= i_data[i];
          end
        end
      end
    end
  end
endmodule
