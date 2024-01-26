//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
`ifndef INCLUDED_PZBCM_SELECTOR_MACROS_SVH
`define INCLUDED_PZBCM_SELECTOR_MACROS_SVH

`define pzbcm_selector_get_sub_n(SUB_N, CURRENT_N) \
begin \
  int half_n; \
  half_n  = (CURRENT_N / 2) + (CURRENT_N % 2); \
  if ((CURRENT_N > 4) && (half_n <= 4)) begin \
    SUB_N = half_n; \
  end \
  else if (CURRENT_N >= 4) begin \
    SUB_N = 4; \
  end \
  else begin \
    SUB_N = CURRENT_N; \
  end \
end

`define pzbcm_define_priority_mux(ENTRIES, TYPE) \
typedef struct packed { \
  logic select; \
  TYPE  data; \
} pzbcm_priority_mux_entry; \
\
function automatic pzbcm_priority_mux_entry __priority_mux( \
  int                       n, \
  pzbcm_priority_mux_entry  entries[ENTRIES] \
); \
  int                       current_n; \
  int                       sub_n; \
  int                       index; \
  int                       next_n; \
  pzbcm_priority_mux_entry  next_entries[ENTRIES]; \
\
  current_n = n; \
  index     = 0; \
  next_n    = 0; \
  while (current_n > 0) begin \
    `pzbcm_selector_get_sub_n(sub_n, current_n) \
    case (sub_n) \
      4: begin \
        case ({entries[index+2].select, entries[index+1].select, entries[index+0].select}) inside \
          3'b??1:   next_entries[next_n]  = entries[index+0]; \
          3'b?1?:   next_entries[next_n]  = entries[index+1]; \
          3'b1??:   next_entries[next_n]  = entries[index+2]; \
          default:  next_entries[next_n]  = entries[index+3]; \
        endcase \
      end \
      3: begin \
        case ({entries[index+1].select, entries[index+0].select}) inside \
          2'b?1:    next_entries[next_n]  = entries[index+0]; \
          2'b1?:    next_entries[next_n]  = entries[index+1]; \
          default:  next_entries[next_n]  = entries[index+2]; \
        endcase \
      end \
      2: begin \
        case ({entries[index+0].select}) inside \
          1'b1:     next_entries[next_n]  = entries[index+0]; \
          default:  next_entries[next_n]  = entries[index+1]; \
        endcase \
      end \
      default: begin \
        next_entries[next_n]  = entries[index+0]; \
      end \
    endcase \
\
    current_n -= sub_n; \
    index     += sub_n; \
    next_n    += 1; \
  end \
\
  if (next_n == 1) begin \
    return next_entries[0]; \
  end \
  else begin \
    return __priority_mux(next_n, next_entries); \
  end \
endfunction \
\
function automatic TYPE priority_mux( \
  logic [ENTRIES-1:0] select, \
  TYPE  [ENTRIES-1:0] data \
); \
  if (ENTRIES > 1) begin \
    pzbcm_priority_mux_entry  entries[ENTRIES]; \
    pzbcm_priority_mux_entry  result; \
\
    for (int i = 0;i < ENTRIES;++i) begin \
      entries[i].select = select[i]; \
      entries[i].data   = data[i]; \
    end \
\
    result  = __priority_mux(ENTRIES, entries); \
    return result.data; \
  end \
  else begin \
    return data[0]; \
  end \
endfunction

`define pzbcm_define_onehot_mux(ENTRIES, TYPE) \
function automatic logic [$bits(TYPE)-1:0] __reduce_or( \
  int                     n, \
  logic [$bits(TYPE)-1:0] data[ENTRIES] \
); \
  int                     current_n; \
  int                     sub_n; \
  int                     index; \
  int                     next_n; \
  logic [$bits(TYPE)-1:0] next_data[ENTRIES]; \
\
  current_n = n; \
  index     = 0; \
  next_n    = 0; \
  while (current_n > 0) begin \
    `pzbcm_selector_get_sub_n(sub_n, current_n) \
    case (sub_n) \
      4:        next_data[next_n] = (data[index+0] | data[index+1]) | (data[index+2] | data[index+3]); \
      3:        next_data[next_n] = (data[index+0] | data[index+1]) | (data[index+2]); \
      2:        next_data[next_n] = (data[index+0] | data[index+1]); \
      default:  next_data[next_n] = (data[index+0]); \
    endcase \
\
    current_n -= sub_n; \
    index     += sub_n; \
    next_n    += 1; \
  end \
\
  if (next_n == 1) begin \
    return next_data[0]; \
  end \
  else begin \
    return __reduce_or(next_n, next_data); \
  end \
endfunction \
\
function automatic TYPE onehot_mux( \
  logic [ENTRIES-1:0] select, \
  TYPE  [ENTRIES-1:0] data \
); \
  if (ENTRIES > 1) begin \
    logic [$bits(TYPE)-1:0] masked_data[ENTRIES]; \
    logic [$bits(TYPE)-1:0] result; \
\
    for (int i = 0;i < ENTRIES;++i) begin \
      masked_data[i]  = data[i] & {($bits(TYPE)){select[i]}}; \
    end \
\
    result  = __reduce_or(ENTRIES, masked_data); \
    return TYPE'(result); \
  end \
  else begin \
    return data[0]; \
  end \
endfunction

`endif
