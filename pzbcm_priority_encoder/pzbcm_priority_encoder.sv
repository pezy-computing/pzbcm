//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
interface pzbcm_priority_encoder #(
  parameter int WIDTH = 2
);
  localparam  int OUT_WIDTH = (WIDTH > 1) ? $clog2(WIDTH) : 1;

  `include  "pzbcm_selector_macros.svh"
  `pzbcm_define_mux_params(WIDTH)
  `pzbcm_define_priority_mux(WIDTH, logic [OUT_WIDTH-1:0])

  function automatic logic [OUT_WIDTH-1:0] encode(
    logic [WIDTH-1:0] in
  );
    if (WIDTH > 1) begin
      pzbcm_priority_mux_entry  entries[WIDTH];
      pzbcm_priority_mux_entry  result;

      for (int i = 0;i < WIDTH;++i) begin
        entries[i].select = in[i];
        entries[i].data   = OUT_WIDTH'(i);
      end

      result  = __priority_mux(entries);
      return result.data;
    end
    else begin
      return OUT_WIDTH'(0);
    end
  endfunction
endinterface
