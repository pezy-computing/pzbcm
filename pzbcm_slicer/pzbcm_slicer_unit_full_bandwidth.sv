//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_slicer_unit_full_bandwidth #(
  parameter int WIDTH         = 1,
  parameter bit DISABLE_MBFF  = 0
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
  logic             valid_0;
  logic [WIDTH-1:0] data_0;
  logic             valid_1;
  logic [WIDTH-1:0] data_1;

  always_comb begin
    o_ready = !valid_1;
  end

  always_comb begin
    o_valid = valid_0;
    o_data  = data_0;
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      valid_0 <= '0;
    end
    else if ((!valid_0) || i_ready) begin
      valid_0 <= i_valid || valid_1;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      valid_1 <= '0;
    end
    else if (i_ready) begin
      valid_1 <= '0;
    end
    else if (valid_0 && (!valid_1)) begin
      valid_1 <= i_valid;
    end
  end

  if (!DISABLE_MBFF) begin : g
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        data_0  <= '0;
      end
      else if ((!valid_0) || i_ready) begin
        if (valid_1) begin
          data_0  <= data_1;
        end
        else if (i_valid) begin
          data_0  <= i_data;
        end
      end
    end

    always_ff @(posedge i_clk) begin
      if (valid_0 && (!valid_1) && (!i_ready) && i_valid) begin
        data_1  <= i_data;
      end
    end
  end
  else begin : g
    for (genvar i = 0;i < WIDTH;++i) begin : g
      logic d_0;
      logic d_1;

      always_comb begin
        data_0[i] = d_0;
        data_1[i] = d_1;
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          d_0 <= '0;
        end
        else if ((!valid_0) || i_ready) begin
          if (valid_1) begin
            d_0 <= d_1;
          end
          else if (i_valid) begin
            d_0 <= i_data[i];
          end
        end
      end

      always_ff @(posedge i_clk) begin
        if (valid_0 && (!valid_1) && (!i_ready) && i_valid) begin
          d_1 <= i_data[i];
        end
      end
    end
  end
endmodule
