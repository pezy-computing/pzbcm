//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
`ifndef INCLUDED_PZBCM_SELECTOR_MACROS_SVH
`define INCLUDED_PZBCM_SELECTOR_MACROS_SVH

`define pzbcm_define_mux_params(ENTRIES) \
typedef struct { \
  int sub_n[ENTRIES]; \
  int index[ENTRIES]; \
  int next_n; \
} pzbcm_mux_params; \
typedef pzbcm_mux_params  pzbcm_define_mux_params_list[(ENTRIES>1)?$clog2(ENTRIES):1]; \
\
function automatic pzbcm_define_mux_params_list define_mux_params_list(int entries); \
  pzbcm_define_mux_params_list  list; \
  int                           max_depth; \
\
  max_depth = $clog2(entries); \
  for (int i = 0;i < max_depth;++i) begin \
    int n; \
    int j; \
\
    if (i == 0) begin \
      n = entries; \
    end \
    else begin \
      n = list[i-1].next_n; \
    end \
\
    j = 0; \
    while (n > 0) begin \
      int half_n; \
      int sub_n; \
\
      half_n  = (n / 2) + (n % 2); \
      if ((n > 4) && (half_n <= 4)) begin \
        sub_n = half_n; \
      end \
      else if (n >= 4) begin \
        sub_n = 4; \
      end \
      else begin \
        sub_n = n; \
      end \
\
      list[i].sub_n[j]  = sub_n; \
      if (j == 0) begin \
        list[i].index[j]  = 0; \
      end \
      else begin \
        list[i].index[j]  = list[i].index[j-1] + list[i].sub_n[j-1]; \
      end \
\
      n -= sub_n; \
      j += 1; \
    end \
\
    list[i].next_n  = j; \
    if (list[i].next_n == 1) begin \
      break; \
    end \
  end \
\
  return list; \
endfunction \
\
function automatic int calc_mux_depth(int entries, pzbcm_define_mux_params_list params_list); \
  int max_depth = $clog2(entries); \
  for (int i = 0;i < max_depth;++i) begin \
    if (params_list[i].next_n == 1) begin \
      return i + 1; \
    end \
  end \
  return 0; \
endfunction \
\
localparam  pzbcm_define_mux_params_list  MUX_PARAMS_LIST = define_mux_params_list(ENTRIES); \
localparam  int                           MUX_DEPTH       = calc_mux_depth(ENTRIES, MUX_PARAMS_LIST);

`define pzbcm_define_priority_mux(ENTRIES, TYPE) \
typedef struct packed { \
  logic select; \
  TYPE  data; \
} pzbcm_priority_mux_entry; \
\
function automatic pzbcm_priority_mux_entry __priority_mux( \
  pzbcm_priority_mux_entry  entries[ENTRIES] \
); \
  pzbcm_priority_mux_entry  next_entries[ENTRIES]; \
  pzbcm_priority_mux_entry  current_entries[ENTRIES]; \
\
  for (int i = 0;i < MUX_DEPTH;++i) begin \
    if (i == 0) begin \
      current_entries = entries; \
    end \
    else begin \
      current_entries = next_entries; \
    end \
\
    for (int j = 0;j < MUX_PARAMS_LIST[i].next_n;++j) begin \
      int sub_n = MUX_PARAMS_LIST[i].sub_n[j]; \
      int index = MUX_PARAMS_LIST[i].index[j]; \
\
      if (sub_n == 4) begin \
        case ({current_entries[index+2].select, current_entries[index+1].select, current_entries[index+0].select}) inside \
          3'b??1:   next_entries[j] = current_entries[index+0]; \
          3'b?1?:   next_entries[j] = current_entries[index+1]; \
          3'b1??:   next_entries[j] = current_entries[index+2]; \
          default:  next_entries[j] = current_entries[index+3]; \
        endcase \
      end \
      else if (sub_n == 3) begin \
        case ({current_entries[index+1].select, current_entries[index+0].select}) inside \
          2'b?1:    next_entries[j] = current_entries[index+0]; \
          2'b1?:    next_entries[j] = current_entries[index+1]; \
          default:  next_entries[j] = current_entries[index+2]; \
        endcase \
      end \
      else if (sub_n == 2) begin \
        case ({current_entries[index+0].select}) inside \
          1'b1:     next_entries[j] = current_entries[index+0]; \
          default:  next_entries[j] = current_entries[index+1]; \
        endcase \
      end \
      else begin \
        next_entries[j] = current_entries[index]; \
      end \
    end \
  end \
\
  if (ENTRIES > 1) begin \
    return next_entries[0]; \
  end \
  else begin \
    return entries[0]; \
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
    result  = __priority_mux(entries); \
    return result.data; \
  end \
  else begin \
    return data[0]; \
  end \
endfunction

`define pzbcm_define_onehot_mux(ENTRIES, TYPE) \
function automatic logic [$bits(TYPE)-1:0] __reduce_or( \
  logic [$bits(TYPE)-1:0] data[ENTRIES] \
); \
  logic [$bits(TYPE)-1:0] current_data[ENTRIES]; \
  logic [$bits(TYPE)-1:0] next_data[ENTRIES]; \
\
  for (int i = 0;i < MUX_DEPTH;++i) begin \
    if (i == 0) begin \
      current_data  = data; \
    end \
    else begin \
      current_data  = next_data; \
    end \
\
    for (int j = 0;j < MUX_PARAMS_LIST[i].next_n;++j) begin \
      int sub_n = MUX_PARAMS_LIST[i].sub_n[j]; \
      int index = MUX_PARAMS_LIST[i].index[j]; \
      case (sub_n) \
        4:        next_data[j]  = (current_data[index+0] | current_data[index+1]) | (current_data[index+2] | current_data[index+3]); \
        3:        next_data[j]  = (current_data[index+0] | current_data[index+1]) | (current_data[index+2]); \
        2:        next_data[j]  = (current_data[index+0] | current_data[index+1]); \
        default:  next_data[j]  = (current_data[index+0]); \
      endcase \
    end \
  end \
\
  if (ENTRIES > 1) begin \
    return next_data[0]; \
  end \
  else begin \
    return data[0]; \
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
    result  = __reduce_or(masked_data); \
    return TYPE'(result); \
  end \
  else begin \
    return data[0]; \
  end \
endfunction

`endif
