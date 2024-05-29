//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_rmw_converter
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG            = '0,
  parameter int               MAX_NP_REQUESTS       = 32,
  parameter bit               SLAVE_SLICER          = 1,
  parameter bit               MASTER_SLICER         = 1,
  parameter bit               SVA_CHECKER           = 1,
  parameter bit               REQUEST_SVA_CHECKER   = SVA_CHECKER,
  parameter bit               RESPONSE_SVA_CHECKER  = SVA_CHECKER
)(
  input var                           i_clk,
  input var                           i_rst_n,
  input var [BUS_CONFIG.id_width-1:0] i_read_id,
  input var                           i_bypass,
  pzcorebus_if.slave                  slave_if,
  pzcorebus_if.master                 master_if
);
  initial begin
    assume (is_memory_profile(BUS_CONFIG));
  end

  localparam  int COUNTER_WIDTH   = $clog2(MAX_NP_REQUESTS + 1);
  localparam  int DATA_FIFO_DEPTH = BUS_CONFIG.max_burst_length;

  typedef enum logic [2:0] {
    PASS_THROUGH,
    FILL_WRITE_DATA,
    SEND_READ_REQUEST,
    WAIT_FOR_READ_RESPONSE,
    DO_NORMAL_WRITE_ACCESS,
    DO_RMW_WRITE_ACCESS
  } pzcorebus_rmw_converter_state;

  typedef logic [BUS_CONFIG.data_width-1:0]                 pzcorebus_data;
  typedef logic [get_byte_enable_width(BUS_CONFIG, 1)-1:0]  pzcorebus_byte_enable;

//--------------------------------------------------------------
//  Command/data aligner
//--------------------------------------------------------------
  pzcorebus_if #(BUS_CONFIG)  aligner_if();

  pzcorebus_command_data_aligner #(
    .BUS_CONFIG           (BUS_CONFIG           ),
    .SLAVE_FIFO           (SLAVE_SLICER         ),
    .COMMAND_DEPTH        (2                    ),
    .DATA_DEPTH           (2                    ),
    .RESPONSE_DEPTH       (2                    ),
    .REQUEST_SVA_CHECKER  (REQUEST_SVA_CHECKER  ),
    .RESPONSE_SVA_CHECKER (0                    )
  ) u_aligner (
    .i_clk      (i_clk      ),
    .i_rst_n    (i_rst_n    ),
    .slave_if   (slave_if   ),
    .master_if  (aligner_if )
  );

//--------------------------------------------------------------
//  RMW converter
//--------------------------------------------------------------
  pzcorebus_if #(BUS_CONFIG)    fifo_if[2]();
  pzcorebus_if #(BUS_CONFIG)    rmw_converter_if();
  pzcorebus_rmw_converter_state state;
  logic                         command_active;
  logic [2:0]                   fifo_empty;
  logic [COUNTER_WIDTH-1:0]     np_access_count;
  logic                         np_access_count_full;
  logic [1:0]                   np_access_count_up_down;
  logic                         partial_write;
  logic                         command_done;
  logic                         data_done;
  logic                         write_access_done;

  //
  //  Slave side control
  //
  always_comb begin
    //  the command fifo and write data fifo need to be empty when a write request is going through the pipeline.
    //  this is to simplify the FSM logic. 'fifo_empty[0]' is used for this purpose.
    command_active  = i_bypass || fifo_if[0].is_command_no_data() || fifo_empty[0];

    case (state)
      PASS_THROUGH: begin
        aligner_if.scmd_accept  = command_active && fifo_if[0].scmd_accept;
        fifo_if[0].mcmd_valid   = command_active && aligner_if.mcmd_valid;
        aligner_if.sdata_accept = command_active && fifo_if[0].sdata_accept;
        fifo_if[0].mdata_valid  = command_active && aligner_if.mdata_valid;
      end
      FILL_WRITE_DATA: begin
        aligner_if.scmd_accept  = '0;
        fifo_if[0].mcmd_valid   = '0;
        aligner_if.sdata_accept = fifo_if[0].sdata_accept;
        fifo_if[0].mdata_valid  = aligner_if.mdata_valid;
      end
      default: begin
        aligner_if.scmd_accept  = '0;
        aligner_if.sdata_accept = '0;
        fifo_if[0].mcmd_valid   = '0;
        fifo_if[0].mdata_valid  = '0;
      end
    endcase

    fifo_if[0].put_request(aligner_if.get_request());
  end

  always_comb begin
    case (state)
      PASS_THROUGH, FILL_WRITE_DATA, SEND_READ_REQUEST: begin
        fifo_if[0].mresp_accept = aligner_if.mresp_accept;
        aligner_if.sresp_valid  = fifo_if[0].sresp_valid;
      end
      DO_RMW_WRITE_ACCESS: begin
        fifo_if[0].mresp_accept = rmw_converter_if.sdata_accept;
        aligner_if.sresp_valid  = '0;
      end
      default: begin
        fifo_if[0].mresp_accept = '0;
        aligner_if.sresp_valid  = '0;
      end
    endcase

    aligner_if.put_response(fifo_if[0].get_response());
  end

  //
  //  conversion logic
  //
  always_comb begin
    case (state)
      PASS_THROUGH: begin
        fifo_if[1].scmd_accept        = (!np_access_count_full) && rmw_converter_if.scmd_accept;
        rmw_converter_if.mcmd_valid   = (!np_access_count_full) && fifo_if[1].mcmd_valid;
        fifo_if[1].sdata_accept       = (!np_access_count_full) && rmw_converter_if.sdata_accept;
        rmw_converter_if.mdata_valid  = (!np_access_count_full) && fifo_if[1].mdata_valid;
      end
      SEND_READ_REQUEST: begin
        fifo_if[1].scmd_accept        = '0;
        rmw_converter_if.mcmd_valid   = (np_access_count == COUNTER_WIDTH'(0)) && fifo_empty[2];
        fifo_if[1].sdata_accept       = '0;
        rmw_converter_if.mdata_valid  = '0;
      end
      DO_NORMAL_WRITE_ACCESS, DO_RMW_WRITE_ACCESS: begin
        fifo_if[1].scmd_accept        = (!command_done) && rmw_converter_if.scmd_accept;
        rmw_converter_if.mcmd_valid   = (!command_done) && fifo_if[1].mcmd_valid;
        fifo_if[1].sdata_accept       = (!data_done   ) && rmw_converter_if.sdata_accept;
        rmw_converter_if.mdata_valid  = (!data_done   ) && fifo_if[1].mdata_valid;
      end
      default: begin
        fifo_if[1].scmd_accept        = '0;
        rmw_converter_if.mcmd_valid   = '0;
        fifo_if[1].sdata_accept       = '0;
        rmw_converter_if.mdata_valid  = '0;
      end
    endcase

    rmw_converter_if.mcmd         = (state == SEND_READ_REQUEST) ? PZCOREBUS_READ : fifo_if[1].mcmd;
    rmw_converter_if.mid          = (state == SEND_READ_REQUEST) ? i_read_id      : fifo_if[1].mid;
    rmw_converter_if.maddr        = fifo_if[1].maddr;
    rmw_converter_if.mlength      = fifo_if[1].mlength;
    rmw_converter_if.mparam       = fifo_if[1].mparam;
    rmw_converter_if.minfo        = fifo_if[1].minfo;
    rmw_converter_if.mdata        = get_mdata(state, fifo_if[1].mdata, fifo_if[1].mdata_byteen, fifo_if[0].sdata);
    rmw_converter_if.mdata_byteen = (state == DO_RMW_WRITE_ACCESS) ? '1 : fifo_if[1].mdata_byteen;
    rmw_converter_if.mdata_last   = fifo_if[1].mdata_last;
  end

  always_comb begin
    rmw_converter_if.mresp_accept = fifo_if[1].mresp_accept;
    fifo_if[1].sresp_valid        = rmw_converter_if.sresp_valid;
    fifo_if[1].put_response(rmw_converter_if.get_response());
  end

  function automatic pzcorebus_data get_mdata(
    pzcorebus_rmw_converter_state state,
    pzcorebus_data                mdata,
    pzcorebus_byte_enable         mdata_byteen,
    pzcorebus_data                sdata
  );
    pzcorebus_data  mask;

    if (state == DO_RMW_WRITE_ACCESS) begin
      for (int i = 0;i < $bits(pzcorebus_byte_enable);++i) begin
        mask[8*i+:8]  = {8{mdata_byteen[i]}};
      end
    end
    else begin
      mask  = '1;
    end

    return (mdata & mask) | (sdata &(~mask));
  endfunction

  //
  //  state
  //
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      state <= PASS_THROUGH;
    end
    else if (i_bypass) begin
      state <= PASS_THROUGH;
    end
    else begin
      case (state)
        PASS_THROUGH: begin
          if (aligner_if.command_with_data_ack()) begin
            if (!aligner_if.write_data_last_ack()) begin
              state <= FILL_WRITE_DATA;
            end
            else if ((aligner_if.mdata_byteen == '1) || aligner_if.is_atomic_command()) begin
              state <= DO_NORMAL_WRITE_ACCESS;
            end
            else begin
              state <= SEND_READ_REQUEST;
            end
          end
        end
        FILL_WRITE_DATA: begin
          if (aligner_if.write_data_last_ack()) begin
            if (partial_write || (aligner_if.mdata_byteen != '1)) begin
              state <= SEND_READ_REQUEST;
            end
            else begin
              state <= DO_NORMAL_WRITE_ACCESS;
            end
          end
        end
        SEND_READ_REQUEST: begin
          if (rmw_converter_if.command_ack()) begin
            state <= WAIT_FOR_READ_RESPONSE;
          end
        end
        WAIT_FOR_READ_RESPONSE: begin
          if (rmw_converter_if.response_last_ack()) begin
            state <= DO_RMW_WRITE_ACCESS;
          end
        end
        DO_NORMAL_WRITE_ACCESS, DO_RMW_WRITE_ACCESS: begin
          if (write_access_done) begin
            state <= PASS_THROUGH;
          end
        end
      endcase
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      partial_write <= '0;
    end
    else if (i_bypass || fifo_if[1].write_data_last_ack()) begin
      partial_write <= '0;
    end
    else if (fifo_if[0].write_data_ack()) begin
      partial_write <= partial_write || (fifo_if[0].mdata_byteen != '1);
    end
  end

  always_comb begin
    write_access_done =
      (rmw_converter_if.command_with_data_ack() && rmw_converter_if.write_data_last_ack()) ||
      (command_done                             && rmw_converter_if.write_data_last_ack()) ||
      (rmw_converter_if.command_with_data_ack() && data_done                             );
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      command_done  <= '0;
      data_done     <= '0;
    end
    else if (i_bypass || write_access_done) begin
      command_done  <= '0;
      data_done     <= '0;
    end
    else if (rmw_converter_if.command_with_data_ack()) begin
      command_done  <= '1;
      data_done     <= '0;
    end
    else if (rmw_converter_if.write_data_last_ack()) begin
      command_done  <= '0;
      data_done     <= '1;
    end
  end

  always_comb begin
    np_access_count_full        = np_access_count == COUNTER_WIDTH'(MAX_NP_REQUESTS);
    np_access_count_up_down[1]  = rmw_converter_if.command_non_posted_ack();
    np_access_count_up_down[0]  = rmw_converter_if.response_last_ack();
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      np_access_count <= COUNTER_WIDTH'(0);
    end
    else if (i_bypass) begin
      np_access_count <= COUNTER_WIDTH'(0);
    end
    else begin
      case (np_access_count_up_down)
        2'b10:  np_access_count <= np_access_count + COUNTER_WIDTH'(1);
        2'b01:  np_access_count <= np_access_count - COUNTER_WIDTH'(1);
      endcase
    end
  end

  //
  //  FIFO
  //
  pzcorebus_fifo #(
    .BUS_CONFIG     (BUS_CONFIG       ),
    .COMMAND_DEPTH  (2                ),
    .DATA_DEPTH     (DATA_FIFO_DEPTH  ),
    .RESPONSE_DEPTH (DATA_FIFO_DEPTH  )
  ) u_fifo (
    .i_clk          (i_clk      ),
    .i_rst_n        (i_rst_n    ),
    .i_clear        ('0         ),
    .o_empty        (fifo_empty ),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (fifo_if[0] ),
    .master_if      (fifo_if[1] )
  );

//--------------------------------------------------------------
//  Master slicer
//--------------------------------------------------------------
  pzcorebus_slicer #(
    .BUS_CONFIG           (BUS_CONFIG           ),
    .STAGES               (1                    ),
    .REQUEST_VALID        (MASTER_SLICER        ),
    .RESPONSE_VALID       (MASTER_SLICER        ),
    .REQUEST_SVA_CHECKER  (0                    ),
    .RESPONSE_SVA_CHECKER (RESPONSE_SVA_CHECKER )
  ) u_master_slicer (
    .i_clk      (i_clk            ),
    .i_rst_n    (i_rst_n          ),
    .slave_if   (rmw_converter_if ),
    .master_if  (master_if        )
  );
endmodule
