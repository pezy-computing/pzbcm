//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_packer_data_fifo
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG  = '0,
  parameter int               DEPTH       = get_max_burst_length(BUS_CONFIG),
  parameter bit               DATA_FF_OUT = 0
)(
  input   var                     i_clk,
  input   var                     i_rst_n,
  input   var                     i_clear,
  output  var                     o_fifo_empty,
  output  var                     o_fifo_full,
  pzcorebus_if.write_data_slave   slave_if,
  pzcorebus_if.write_data_master  master_if
);
  typedef logic [get_packed_write_data_width(BUS_CONFIG, 1)-1:0]  pzcorebus_packed_write_data;

  localparam  int POINTER_WIDTH = $clog2(DEPTH);
  localparam  int COUNTER_WIDTH = $clog2(DEPTH + 1);

  logic [POINTER_WIDTH-1:0]         write_pointer;
  logic [POINTER_WIDTH-1:0]         read_pointer;
  logic                             fifo_push;
  logic                             fifo_pop;
  pzcorebus_packed_write_data [1:0] fifo_data;
  logic                             fifo_empty;
  logic                             fifo_full;
  logic                             slicer_push;
  logic                             slicer_pop;
  pzcorebus_packed_write_data       slicer_data;
  logic                             slicer_empty;
  logic                             slicer_almost_full;
  logic                             slicer_full;

  always_comb begin
    o_fifo_empty  = fifo_empty && slicer_empty;
    o_fifo_full   = fifo_full  && slicer_full;
  end

//--------------------------------------------------------------
//  FIFO
//--------------------------------------------------------------
  always_comb begin
    slave_if.sdata_accept = !fifo_full;
    fifo_push             = slave_if.write_data_ack();
    fifo_data[0]          = slave_if.get_packed_write_data();
  end

  always_comb begin
    fifo_pop  = (!fifo_empty) && (!slicer_almost_full);
  end

  pzbcm_fifo_controller #(
    .DEPTH        (DEPTH  ),
    .FLAG_FF_OUT  (1      ),
    .DATA_FF_OUT  (0      )
  ) u_controller (
    .i_clk            (i_clk          ),
    .i_rst_n          (i_rst_n        ),
    .i_clear          (i_clear        ),
    .o_empty          (fifo_empty     ),
    .o_almost_full    (),
    .o_full           (fifo_full      ),
    .i_push           (fifo_push      ),
    .i_data           ('0             ),
    .i_pop            (fifo_pop       ),
    .o_word_count     (),
    .o_write_pointer  (write_pointer  ),
    .o_write_to_ff    (),
    .o_write_to_ram   (),
    .o_read_pointer   (read_pointer   ),
    .o_read_from_ram  ()
  );

  `ifndef PZCOREBUS_PACKER_DATA_RAM
    `define PZCOREBUS_PACKER_DATA_RAM pzcorebus_packer_data_ram_default
  `endif

  `PZCOREBUS_PACKER_DATA_RAM #(
    .WORD_SIZE      (DEPTH                              ),
    .ADDRESS_WIDTH  (POINTER_WIDTH                      ),
    .DATA_WIDTH     ($bits(pzcorebus_packed_write_data) )
  ) u_ram (
    .i_clk            (i_clk          ),
    .i_write_valid    (fifo_push      ),
    .i_write_address  (write_pointer  ),
    .i_write_data     (fifo_data[0]   ),
    .i_read_valid     (fifo_pop       ),
    .i_read_address   (read_pointer   ),
    .o_read_data      (fifo_data[1]   )
  );

//--------------------------------------------------------------
//  Slicer
//--------------------------------------------------------------
  always_comb begin
    master_if.mdata_valid = !slicer_empty;
    master_if.put_packed_write_data(slicer_data);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      slicer_push <= '0;
    end
    else begin
      slicer_push <= fifo_pop;
    end
  end

  always_comb begin
    slicer_pop  = master_if.write_data_ack();
  end

  pzbcm_fifo #(
    .TYPE         (pzcorebus_packed_write_data  ),
    .DEPTH        (3                            ),
    .THRESHOLD    (2                            ),
    .FLAG_FF_OUT  (1                            ),
    .DATA_FF_OUT  (DATA_FF_OUT                  )
  ) u_slicer (
    .i_clk          (i_clk              ),
    .i_rst_n        (i_rst_n            ),
    .i_clear        (i_clear            ),
    .o_empty        (slicer_empty       ),
    .o_almost_full  (slicer_almost_full ),
    .o_full         (slicer_full        ),
    .o_word_count   (),
    .i_push         (slicer_push        ),
    .i_data         (fifo_data[1]       ),
    .i_pop          (slicer_pop         ),
    .o_data         (slicer_data        )
  );
endmodule
