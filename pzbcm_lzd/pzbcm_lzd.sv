//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//
//========================================
interface pzbcm_lzd #(
  parameter int WIDTH     = 8,
  parameter bit FROM_MSB  = 1
);
  localparam  int NIBBLES     = (WIDTH + 3) / 4;
  localparam  int COUNT_WIDTH = $clog2(WIDTH + 1);

  typedef logic [3:0]                     pzbcm_lzd_nibble;
  typedef pzbcm_lzd_nibble  [NIBBLES-1:0] pzbcm_lzd_nibbles;

  `include  "pzbcm_selector_macros.svh"
  `pzbcm_define_mux_params(NIBBLES + 1)
  `pzbcm_define_priority_mux(NIBBLES + 1, logic [COUNT_WIDTH-1:0])

  function automatic logic [COUNT_WIDTH-1:0] get_leading_zero_count(
    logic [WIDTH-1:0] bits
  );
    pzbcm_lzd_nibbles         nibbles;
    pzbcm_priority_mux_entry  mux_entries[NIBBLES+1];
    pzbcm_priority_mux_entry  result;

    if (FROM_MSB) begin
      nibbles = pzbcm_lzd_nibbles'({<<{bits}});
    end
    else begin
      nibbles = pzbcm_lzd_nibbles'(bits);
    end

    for (int i = 0;i < NIBBLES;++i) begin
      logic       all_zero;
      logic [1:0] local_count;
      {all_zero, local_count} = __calc_nlc(nibbles[i]);
      mux_entries[i].select   = !all_zero;
      mux_entries[i].data     = {(COUNT_WIDTH-2)'(i), local_count};
    end
    mux_entries[NIBBLES].select = '1;
    mux_entries[NIBBLES].data   = COUNT_WIDTH'(WIDTH);

    result  = __priority_mux(mux_entries);
    return result.data;
  endfunction

  function automatic logic [2:0] __calc_nlc(logic [3:0] nibble);
    logic [2:0] result;
    result[2] = ~|nibble;
    result[1] = ~|nibble[1:0];
    result[0] = ~(nibble[0] | ((~nibble[1]) & nibble[2]));
    return result;
  endfunction
endinterface
