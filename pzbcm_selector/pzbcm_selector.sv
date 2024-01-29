//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzbcm_selector
  import  pzbcm_selector_pkg::*;
#(
  parameter int                 WIDTH         = 1,
  parameter type                TYPE          = logic [WIDTH-1:0],
  parameter int                 ENTRIES       = 2,
  parameter pzbcm_selector_type SELECTOR_TYPE = PZBCM_SELECTOR_BINARY,
  parameter TYPE                DEFAULT       = TYPE'(0)
);
  `include  "pzbcm_selector_macros.svh"

  localparam  int INDEX_WIDTH   = calc_binary_index_width(ENTRIES);
  localparam  int SELECT_WIDTH  = calc_select_width(SELECTOR_TYPE, ENTRIES);

  `pzbcm_define_mux_params(ENTRIES)
  `pzbcm_define_priority_mux(ENTRIES, TYPE)
  `pzbcm_define_onehot_mux(ENTRIES, TYPE)

  function automatic TYPE binary_mux(
    logic [INDEX_WIDTH-1:0] select,
    TYPE  [ENTRIES-1:0]     data
  );
    if (ENTRIES > 1) begin
      return data[select];
    end
    else begin
      return data[0];
    end
  endfunction

  function automatic TYPE mux(
    logic [SELECT_WIDTH-1:0]  select,
    TYPE  [ENTRIES-1:0]       data
  );
    case (SELECTOR_TYPE)
      PZBCM_SELECTOR_BINARY:
        return binary_mux(INDEX_WIDTH'(select), data);
      PZBCM_SELECTOR_PRIORITY:
        return priority_mux(ENTRIES'(select), data);
      default:
        return onehot_mux(ENTRIES'(select), data);
    endcase
  endfunction

  function automatic TYPE [ENTRIES-1:0] vector_demux(
    logic [ENTRIES-1:0] select,
    TYPE                data
  );
    TYPE  [ENTRIES-1:0] out;

    for (int i = 0;i < ENTRIES;++i) begin
      if (select[i]) begin
        out[i]  = data;
      end
      else begin
        out[i]  = DEFAULT;
      end
    end

    return out;
  endfunction

  function automatic TYPE [ENTRIES-1:0] binary_demux(
    logic [INDEX_WIDTH-1:0] select,
    TYPE                    data
  );
    TYPE  [ENTRIES-1:0] out;

    for (int i = 0;i < ENTRIES;++i) begin
      if (select == INDEX_WIDTH'(i)) begin
        out[i]  = data;
      end
      else begin
        out[i]  = DEFAULT;
      end
    end

    return out;
  endfunction

  function automatic TYPE [ENTRIES-1:0] demux(
    logic [SELECT_WIDTH-1:0]  select,
    TYPE                      data
  );
    if (SELECTOR_TYPE == PZBCM_SELECTOR_BINARY) begin
      return binary_demux(INDEX_WIDTH'(select), data);
    end
    else begin
      return vector_demux(ENTRIES'(select), data);
    end
  endfunction
endinterface
