//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzbcm_gray #(
  parameter int WIDTH = 4
);
  function automatic logic [WIDTH-1:0] encode(
    logic [WIDTH-1:0] binary
  );
    return {1'b0, binary[WIDTH-1:1]} ^ binary;
  endfunction

  function automatic logic [WIDTH-1:0] decode(
    logic [WIDTH-1:0] gray
  );
    logic [WIDTH-1:0] binary;
    logic [WIDTH-1:0] temp;

    binary  = WIDTH'(0);
    temp    = gray;
    for (int i = 0;i < WIDTH;++i) begin
      binary  = binary ^ temp;
      temp    = {1'b0, temp[WIDTH-1:1]};
    end

    return binary;
  endfunction
endinterface
