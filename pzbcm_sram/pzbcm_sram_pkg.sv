//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//
//========================================
package pzbcm_sram_pkg;
  typedef struct packed {
    shortint  words;
    shortint  data_width;
    bit       single_port_ram;
    bit       dual_clock;
    shortint  read_latency;
    int       id;
  } pzbcm_sram_params;

  function automatic int get_total_words(pzbcm_sram_params sram_prams, int banks);
    return sram_prams.words * banks;
  endfunction

  function automatic int get_pointer_width(pzbcm_sram_params sram_prams, int banks);
    int total_words = get_total_words(sram_prams, banks);
    if (total_words > 1) begin
      return $clog2(total_words);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_bank_width(int banks);
    if (banks > 1) begin
      return $clog2(banks);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_ram_pointer_width(pzbcm_sram_params sram_prams);
    if (sram_prams.words > 1) begin
      return $clog2(sram_prams.words);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic int get_ram_pointer_lsb(int banks, bit bank_lsb);
    if (bank_lsb && (banks > 1)) begin
      return get_bank_width(banks);
    end
    else begin
      return 0;
    end
  endfunction
endpackage
