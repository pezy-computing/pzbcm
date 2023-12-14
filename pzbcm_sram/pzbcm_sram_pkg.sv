//========================================
//
// Copyright (c) 2023 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
package pzbcm_sram_pkg;
  typedef struct packed {
    shortint  words;
    shortint  data_width;
    shortint  banks;
    bit       bank_lsb;
    bit       single_port_ram;
    bit       single_clock;
    shortint  read_latency;
    int       id;
  } pzbcm_sram_params;

  function automatic shortint calc_pointer_width(shortint words);
    if (words > 1) begin
      return $clog2(words);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic shortint calc_bank_width(shortint banks);
    if (banks > 1) begin
      return $clog2(banks);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic shortint calc_ram_words(shortint words, shortint banks);
    return words / banks;
  endfunction

  function automatic shortint calc_ram_pointer_width(shortint words, shortint banks);
    shortint  ram_words = calc_ram_words(words, banks);
    if (ram_words > 1) begin
      return $clog2(ram_words);
    end
    else begin
      return 1;
    end
  endfunction

  function automatic shortint get_ram_pointer_lsb(shortint banks, bit bank_lsb);
    if (bank_lsb && (banks > 1)) begin
      return calc_bank_width(banks);
    end
    else begin
      return 0;
    end
  endfunction
endpackage
