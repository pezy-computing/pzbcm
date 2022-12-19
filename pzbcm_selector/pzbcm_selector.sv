//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
interface pzbcm_selector
  import  pzbcm_selector_pkg::*;
#(
  parameter int                 WIDTH         = 1,
  parameter type                TYPE          = logic [WIDTH-1:0],
  parameter int                 ENTRIES       = 2,
  parameter pzbcm_selector_type SELECTOR_TYPE = PZBCM_SELECTOR_BINARY,
  parameter TYPE                DEFAULT       = TYPE'(0)
);
  localparam  int INDEX_WIDTH   = calc_binary_index_width(ENTRIES);
  localparam  int SELECT_WIDTH  = calc_select_width(SELECTOR_TYPE, ENTRIES);
  localparam  int DATA_WIDTH    = $bits(TYPE);

  typedef struct packed {
    logic select;
    TYPE  data;
  } pzbcm_priority_mux_entry;

  function automatic int get_sub_n(int current_n);
    int half_n;
    half_n  = (current_n / 2) + (current_n % 2);
    if ((current_n > 4) && (half_n <= 4)) begin
      return half_n;
    end
    else if (current_n >= 4) begin
      return 4;
    end
    else begin
      return current_n;
    end
  endfunction

  function automatic pzbcm_priority_mux_entry __priority_mux(
    int                                     n,
    pzbcm_priority_mux_entry  [ENTRIES-1:0] entries
  );
    int                                     current_n;
    int                                     index;
    int                                     next_n;
    pzbcm_priority_mux_entry  [ENTRIES-1:0] next_entries;

    current_n = n;
    index     = 0;
    next_n    = 0;
    while (current_n > 0) begin
      int sub_n;

      sub_n = get_sub_n(current_n);
      case (sub_n)
        4: begin
          case (1'b1)
            entries[index+0].select:  next_entries[next_n]  = entries[index+0];
            entries[index+1].select:  next_entries[next_n]  = entries[index+1];
            entries[index+2].select:  next_entries[next_n]  = entries[index+2];
            default:                  next_entries[next_n]  = entries[index+3];
          endcase
        end
        3: begin
          case (1'b1)
            entries[index+0].select:  next_entries[next_n]  = entries[index+0];
            entries[index+1].select:  next_entries[next_n]  = entries[index+1];
            default:                  next_entries[next_n]  = entries[index+2];
          endcase
        end
        2: begin
          case (1'b1)
            entries[index+0].select:  next_entries[next_n]  = entries[index+0];
            default:                  next_entries[next_n]  = entries[index+1];
          endcase
        end
        default: begin
          next_entries[next_n]  = entries[index];
        end
      endcase

      current_n -= sub_n;
      index     += sub_n;
      next_n    += 1;
    end

    if (next_n == 1) begin
      return next_entries[0];
    end
    else begin
      return __priority_mux(next_n, next_entries);
    end
  endfunction

  function automatic TYPE priority_mux(
    logic [ENTRIES-1:0] select,
    TYPE  [ENTRIES-1:0] data
  );
    if (ENTRIES > 1) begin
      pzbcm_priority_mux_entry  [ENTRIES-1:0] entries;
      pzbcm_priority_mux_entry                result;

      for (int i = 0;i < ENTRIES;++i) begin
        entries[i].select = select[i];
        entries[i].data   = data[i];
      end

      result  = __priority_mux(ENTRIES, entries);
      return result.data;
    end
    else begin
      return data[0];
    end
  endfunction

  function automatic logic [DATA_WIDTH-1:0] __reduce_or(
    int                                 n,
    logic [ENTRIES-1:0][DATA_WIDTH-1:0] data
  );
    int                                 current_n;
    int                                 index;
    int                                 next_n;
    logic [ENTRIES-1:0][DATA_WIDTH-1:0] next_data;

    current_n = n;
    index     = 0;
    next_n    = 0;
    while (current_n > 0) begin
      int sub_n;

      sub_n = get_sub_n(current_n);
      if (sub_n == 4) begin
        next_data[next_n] = (data[index+0] | data[index+1]) | (data[index+2] | data[index+3]);
      end
      else if (sub_n == 3) begin
        next_data[next_n] = data[index+0] | data[index+1] | data[index+2];
      end
      else if (sub_n == 2) begin
        next_data[next_n] = data[index+0] | data[index+1];
      end
      else begin
        next_data[next_n] = data[index+0];
      end

      current_n -= sub_n;
      index     += sub_n;
      next_n    += 1;
    end

    if (next_n == 1) begin
      return next_data[0];
    end
    else begin
      return __reduce_or(next_n, next_data);
    end
  endfunction

  function automatic TYPE onehot_mux(
    logic [ENTRIES-1:0] select,
    TYPE  [ENTRIES-1:0] data
  );
    if (ENTRIES > 1) begin
      logic [ENTRIES-1:0][DATA_WIDTH-1:0] masked_data;
      logic [DATA_WIDTH-1:0]              result;

      for (int i = 0;i < ENTRIES;++i) begin
        masked_data[i]  = data[i] & {DATA_WIDTH{select[i]}};
      end

      result  = __reduce_or(ENTRIES, masked_data);
      return TYPE'(result);
    end
    else begin
      return data[0];
    end
  endfunction

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
