//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzbcm_counter #(
  parameter   int             WIDTH         = 2,
  parameter   bit [WIDTH-1:0] MAX_COUNT     = '1,
  parameter   bit [WIDTH-1:0] MIN_COUNT     = '0,
  parameter   bit [WIDTH-1:0] INITIAL_COUNT = MIN_COUNT,
  parameter   bit             WRAP_AROUND   = 1,
  localparam  type            COUNT         = logic [WIDTH-1:0]
)(
  input   var       i_clk,
  input   var       i_rst_n,
  input   var       i_clear,
  input   var       i_set,
  input   var COUNT i_set_value,
  input   var       i_up,
  input   var       i_down,
  output  var COUNT o_count,
  output  var COUNT o_count_next,
  output  var       o_wrap_around
);
  COUNT count;
  COUNT count_next;

  assign  o_count       = count;
  assign  o_count_next  = count_next;

  assign  count_next  = get_count_next(
    i_clear, i_set, i_set_value, i_up, i_down, count
  );
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      count <= INITIAL_COUNT;
    end
    else begin
      count <= count_next;
    end
  end

  if (WRAP_AROUND) begin : g
    assign  o_wrap_around = get_wrap_around_flag(i_clear, i_set, i_up, i_down, count);
  end
  else begin : g
    assign  o_wrap_around = '0;
  end

  function automatic COUNT get_count_next(
    input logic clear,
    input logic set,
    input COUNT set_value,
    input logic up,
    input logic down,
    input COUNT current_count
  );
    case (1'b1)
      clear:            return INITIAL_COUNT;
      set:              return set_value;
      (up && (!down)):  return count_up(current_count);
      (down && (!up)):  return count_down(current_count);
      default:          return current_count;
    endcase
  endfunction

  function automatic COUNT count_up(
    input COUNT current_count
  );
    if (count == MAX_COUNT) begin
      return (WRAP_AROUND) ? MIN_COUNT : MAX_COUNT;
    end
    else begin
      return current_count + 1;
    end
  endfunction

  function automatic COUNT count_down(
    input COUNT current_count
  );
    if (count == MIN_COUNT) begin
      return (WRAP_AROUND) ? MAX_COUNT : MIN_COUNT;
    end
    else begin
      return current_count - 1;
    end
  endfunction

  function automatic logic get_wrap_around_flag(
    input logic clear,
    input logic set,
    input logic up,
    input logic down,
    input COUNT current_count
  );
    logic [1:0] up_down;
    up_down = {up, down};
    if (clear || set) begin
      return '0;
    end
    else if ((current_count == MAX_COUNT) && (up_down == 2'b10)) begin
      return '1;
    end
    else if ((current_count == MIN_COUNT) && (up_down == 2'b01)) begin
      return '1;
    end
    else begin
      return '0;
    end
  endfunction
endmodule
