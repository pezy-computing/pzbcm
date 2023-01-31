//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzbcm_fifo_controller #(
  parameter   type  TYPE              = logic,
  parameter   int   DEPTH             = 8,
  parameter   int   THRESHOLD         = DEPTH,
  parameter   bit   FLAG_FF_OUT       = 1,
  parameter   bit   DATA_FF_OUT       = 1,
  parameter   int   RAM_WORDS         = (DATA_FF_OUT) ? DEPTH - 1 : DEPTH,
  parameter   int   RAM_POINTER_WIDTH = (RAM_WORDS >= 2) ? $clog2(RAM_WORDS) : 1,
  parameter   int   MATCH_COUNT_WIDTH = 0,
  parameter   int   POINTER_WIDTH     = (DEPTH >= 2) ? $clog2(DEPTH) : 1,
  localparam  type  RAM_POINTER       = logic [RAM_POINTER_WIDTH-1:0],
  localparam  type  POINTER           = logic [POINTER_WIDTH-1:0],
  localparam  type  COUNTER           = logic [$clog2(DEPTH+1)-1:0]
)(
  input   var             i_clk,
  input   var             i_rst_n,
  input   var             i_clear,
  output  var             o_empty,
  output  var             o_almost_full,
  output  var             o_full,
  output  var COUNTER     o_word_count,
  input   var             i_push,
  input   var TYPE        i_data,
  input   var             i_pop,
  output  var RAM_POINTER o_write_pointer,
  output  var             o_write_to_ff,
  output  var             o_write_to_ram,
  output  var RAM_POINTER o_read_pointer,
  output  var             o_read_from_ram
);
  typedef struct packed {
    logic empty;
    logic almost_full;
    logic full;
  } s_status_flag;

  logic         push;
  logic         pop;
  logic [1:0]   push_pop;
  COUNTER       word_counter;
  COUNTER       word_counter_next;
  logic         word_counter_eq_1;
  logic         word_counter_eq_2;
  logic         word_counter_ge_2;
  s_status_flag status_flag;
  logic         write_to_ff;
  logic         write_to_ram;
  RAM_POINTER   ram_write_pointer;
  logic         read_from_ram;
  RAM_POINTER   ram_read_pointer;
  logic         ram_empty_next;
  logic         match_data;
  logic         last_pop_data;

  always_comb begin
    push      = i_push && ((!status_flag.full) && (!match_data));
    pop       = i_pop  && (!status_flag.empty) && last_pop_data;
    push_pop  = {push, pop};
  end

//--------------------------------------------------------------
//  word counter
//--------------------------------------------------------------
  always_comb begin
    o_word_count  = word_counter;
  end

  always_comb begin
    case (push_pop)
      2'b10:    word_counter_next = word_counter + COUNTER'(1);
      2'b01:    word_counter_next = word_counter - COUNTER'(1);
      default:  word_counter_next = word_counter;
    endcase
  end

  always_comb begin
    word_counter_eq_1 = (DEPTH >= 1) && (word_counter == COUNTER'(1));
    word_counter_eq_2 = (DEPTH >= 2) && (word_counter == COUNTER'(2));
    word_counter_ge_2 = (DEPTH >= 2) && (word_counter >= COUNTER'(2));
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      word_counter  <= '0;
    end
    else if (i_clear) begin
      word_counter  <= '0;
    end
    else if (push || pop) begin
      word_counter  <= word_counter_next;
    end
  end

//--------------------------------------------------------------
//  status flag
//--------------------------------------------------------------
  always_comb begin
    o_empty       = status_flag.empty;
    o_almost_full = status_flag.almost_full;
    o_full        = status_flag.full && (!match_data);
  end

  if (FLAG_FF_OUT) begin : g_flag_ff_out
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        status_flag <= '{empty: '1, default: '0};
      end
      else if (i_clear) begin
        status_flag <= '{empty: '1, default: '0};
      end
      else if (pop || push) begin
        status_flag <= get_status_flag(word_counter_next);
      end
    end
  end
  else begin : g_flag_logic_out
    always_comb begin
      status_flag = get_status_flag(word_counter);
    end
  end

  function automatic s_status_flag get_status_flag(COUNTER word_count);
    s_status_flag flag;
    flag.empty        = word_count == 0;
    flag.almost_full  = word_count >= THRESHOLD;
    flag.full         = word_count >= DEPTH;
    return flag;
  endfunction

//--------------------------------------------------------------
//  write/read pointer
//--------------------------------------------------------------
  always_comb begin
    o_write_pointer = ram_write_pointer;
    o_write_to_ff   = write_to_ff;
    o_write_to_ram  = write_to_ram;
    o_read_pointer  = ram_read_pointer;
    o_read_from_ram = read_from_ram;
  end

  if (DATA_FF_OUT) begin : g_data_ff_out
    always_comb begin
      write_to_ff     = push && ((word_counter_eq_1 && (pop == '1)) || status_flag.empty);
      write_to_ram    = push && ((word_counter_eq_1 && (pop == '0)) || word_counter_ge_2);
      read_from_ram   = pop && word_counter_ge_2;
      ram_empty_next  = read_from_ram && (!write_to_ram) && word_counter_eq_2;
    end
  end
  else begin : g_data_ram_out
    always_comb begin
      write_to_ff     = '0;
      write_to_ram    = push;
      read_from_ram   = pop;
      ram_empty_next  = read_from_ram && (!write_to_ram) && word_counter_eq_1;
    end
  end

  if (RAM_WORDS >= 2) begin : g_multi_word_ram
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        ram_write_pointer <= RAM_POINTER'(0);
      end
      else if (i_clear) begin
        ram_write_pointer <= RAM_POINTER'(0);
      end
      else if (ram_empty_next) begin
        ram_write_pointer <= ram_read_pointer;
      end
      else if (write_to_ram) begin
        if (ram_write_pointer == RAM_POINTER'(RAM_WORDS - 1)) begin
          ram_write_pointer <= RAM_POINTER'(0);
        end
        else begin
          ram_write_pointer <= ram_write_pointer + RAM_POINTER'(1);
        end
      end
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        ram_read_pointer  <= RAM_POINTER'(0);
      end
      else if (i_clear) begin
        ram_read_pointer  <= RAM_POINTER'(0);
      end
      else if (ram_empty_next) begin
        ram_read_pointer  <= ram_read_pointer;
      end
      else if (read_from_ram) begin
        if (ram_read_pointer == RAM_POINTER'(RAM_WORDS - 1)) begin
          ram_read_pointer  <= RAM_POINTER'(0);
        end
        else begin
          ram_read_pointer  <= ram_read_pointer + RAM_POINTER'(1);
        end
      end
    end
  end
  else begin : g_single_word_ram
    always_comb begin
      ram_write_pointer = RAM_POINTER'(0);
      ram_read_pointer  = RAM_POINTER'(0);
    end
  end

//--------------------------------------------------------------
//  data match
//--------------------------------------------------------------
  if (MATCH_COUNT_WIDTH > 0) begin : g_data_match
    logic [DEPTH-1:0][MATCH_COUNT_WIDTH-1:0]  match_count;
    logic [DEPTH-1:0]                         match_count_full;
    logic [DEPTH-1:0]                         match_count_eq_1;
    POINTER [1:0]                             write_pointer;
    POINTER                                   read_pointer;
    TYPE                                      data;

    if (DEPTH == RAM_WORDS) begin : g_pointer
      always_comb begin
        write_pointer[0]  = ram_write_pointer;
        read_pointer      = ram_read_pointer;
      end
    end
    else begin : g_pointer
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          write_pointer[0]  <= POINTER'(0);
        end
        else if (i_clear) begin
          write_pointer[0]  <= POINTER'(0);
        end
        else if (push) begin
          if (write_pointer[0] == POINTER'(DEPTH - 1)) begin
            write_pointer[0]  <= POINTER'(0);
          end
          else begin
            write_pointer[0]  <= write_pointer[0] + POINTER'(1);
          end
        end
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          read_pointer  <= POINTER'(0);
        end
        else if (i_clear) begin
          read_pointer  <= POINTER'(0);
        end
        else if (pop) begin
          if (read_pointer == POINTER'(DEPTH - 1)) begin
            read_pointer  <= POINTER'(0);
          end
          else begin
            read_pointer  <= read_pointer + POINTER'(1);
          end
        end
      end
    end

    always_comb begin
      if (write_pointer[0] == POINTER'(0)) begin
        write_pointer[1]  = POINTER'(DEPTH - 1);
      end
      else begin
        write_pointer[1]  = write_pointer[0] - POINTER'(1);
      end
    end

    always_ff @(posedge i_clk) begin
      if (push) begin
        data  <= i_data;
      end
    end

    always_comb begin
      match_data    = (!status_flag.empty) && (i_data == data) && (!match_count_full[write_pointer[1]]);
      last_pop_data = match_count_eq_1[read_pointer];
    end

    for (genvar i = 0;i < DEPTH;++i) begin : g_match_count
      logic [1:0] up;
      logic       down;

      always_comb begin
        match_count_full[i] = match_count[i] == '1;
        match_count_eq_1[i] = match_count[i] == MATCH_COUNT_WIDTH'(1);
      end

      always_comb begin
        up[0] = (match_data == '0) && (write_pointer[0] == POINTER'(i)) && push;
        up[1] = (match_data == '1) && (write_pointer[1] == POINTER'(i)) && i_push;
        down  = (!status_flag.empty) && (read_pointer == POINTER'(i)) && i_pop;
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          match_count[i]  <= MATCH_COUNT_WIDTH'(0);
        end
        else if (i_clear) begin
          match_count[i]  <= MATCH_COUNT_WIDTH'(0);
        end
        else if (up != '0) begin
          match_count[i]  <= match_count[i] + MATCH_COUNT_WIDTH'(1);
        end
        else if (down) begin
          match_count[i]  <= match_count[i] - MATCH_COUNT_WIDTH'(1);
        end
      end
    end
  end
  else begin : g
    always_comb begin
      match_data    = '0;
      last_pop_data = '1;
    end
  end
endmodule
