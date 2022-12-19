//==========================================================
//
// PEZY Computing Confidential
//
// ---------------------------------------------------------
//                   Copyright (c) 2022 PEZY Computing, K.K.
//                                      All Rights Reserved.
//==========================================================
module pzbcm_async_handshake #(
  parameter int                   WIDTH               = 8,
  parameter type                  TYPE                = logic [WIDTH-1:0],
  parameter int                   STAGES              = `PZBCM_SYNCHRONIZER_DEFAULT_STAGES,
  parameter bit                   INITIALIZE_DATA_OUT = 1,
  parameter bit [$bits(TYPE)-1:0] INITIAL_DATA_OUT    = '0
)(
  input   var       is_clk,
  input   var       is_rst_n,
  input   var       is_valid,
  output  var       os_ready,
  input   var TYPE  is_data,
  input   var       id_clk,
  input   var       id_rst_n,
  output  var       od_valid,
  input   var       id_ready,
  output  var TYPE  od_data
);
  logic source_state[2];
  logic destination_state[2];
  TYPE  latched_data;

//--------------------------------------------------------------
//  Source Side
//--------------------------------------------------------------
  if (1) begin : g_source_side
    logic ready;
    logic state;
    logic destination_state_changed;

    assign  os_ready  = ready;
    always_ff @(posedge is_clk, negedge is_rst_n) begin
      if (!is_rst_n) begin
        ready <= '1;
      end
      else if ((!ready) && destination_state_changed) begin
        ready <= '1;
      end
      else if (is_valid) begin
        ready <= '0;
      end
    end

    always_ff @(posedge is_clk) begin
      if (is_valid && ready) begin
        latched_data  <= is_data;
      end
    end

    assign  source_state[0] = state;
    always_ff @(posedge is_clk, negedge is_rst_n) begin
      if (!is_rst_n) begin
        state <= '0;
      end
      else if (is_valid && ready) begin
        state <= ~state;
      end
    end

    pzbcm_edge_detector #(
      .WIDTH          (1  ),
      .INITIAL_VALUE  ('0 )
    ) u_edge_detector (
      .i_clk      (is_clk                     ),
      .i_rst_n    (is_rst_n                   ),
      .i_clear    ('0                         ),
      .i_d        (destination_state[1]       ),
      .o_edge     (destination_state_changed  ),
      .o_posedge  (),
      .o_negedge  ()
    );
  end

//--------------------------------------------------------------
//  Synchronizers
//--------------------------------------------------------------
  pzbcm_synchronizer #(
    .WIDTH  (1      ),
    .STAGES (STAGES )
  ) u_s_to_d (
    .i_clk    (id_clk           ),
    .i_rst_n  (id_rst_n         ),
    .i_d      (source_state[0]  ),
    .o_d      (source_state[1]  )
  );

  pzbcm_synchronizer #(
    .WIDTH  (1      ),
    .STAGES (STAGES )
  ) u_d_to_s (
    .i_clk    (is_clk               ),
    .i_rst_n  (is_rst_n             ),
    .i_d      (destination_state[0] ),
    .o_d      (destination_state[1] )
  );

//--------------------------------------------------------------
//  Destination Side
//--------------------------------------------------------------
  if (1) begin : g_destination_side
    logic valid;
    TYPE  data;
    logic state;
    logic source_state_changed;

    assign  od_valid  = valid;
    always_ff @(posedge id_clk, negedge id_rst_n) begin
      if (!id_rst_n) begin
        valid <= '0;
      end
      else if (valid && id_ready) begin
        valid <= '0;
      end
      else if ((!valid) && source_state_changed) begin
        valid <= '1;
      end
    end

    assign  od_data = data;
    if (INITIALIZE_DATA_OUT) begin : g
      always_ff @(posedge id_clk, negedge id_rst_n) begin
        if (!id_rst_n) begin
          data  <= TYPE'(INITIAL_DATA_OUT);
        end
        else if ((!valid) && source_state_changed) begin
          data  <= latched_data;
        end
      end
    end
    else begin : g
      always_ff @(posedge id_clk) begin
        if ((!valid) && source_state_changed) begin
          data  <= latched_data;
        end
      end
    end

    assign  destination_state[0]  = state;
    always_ff @(posedge id_clk, negedge id_rst_n) begin
      if (!id_rst_n) begin
        state <= '0;
      end
      else if (valid && id_ready) begin
        state <= ~state;
      end
    end

    pzbcm_edge_detector #(
      .WIDTH          (1  ),
      .INITIAL_VALUE  ('0 )
    ) u_edge_detector (
      .i_clk      (id_clk               ),
      .i_rst_n    (id_rst_n             ),
      .i_clear    ('0                   ),
      .i_d        (source_state[1]      ),
      .o_edge     (source_state_changed ),
      .o_posedge  (),
      .o_negedge  ()
    );
  end
endmodule
