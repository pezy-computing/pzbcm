//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
module pzcorebus_command_data_aligner_core
  import  pzcorebus_pkg::*;
#(
  parameter   pzcorebus_config  BUS_CONFIG              = '0,
  parameter   bit               WAIT_FOR_DATA           = 0,
  parameter   bit               THROUGH_NO_DATA_COMMAND = 0,
  parameter   bit               RELAX_MODE              = 1,
  parameter   bit               SLAVE_FIFO              = 0,
  parameter   int               COMMAND_DEPTH           = 2,
  parameter   int               DATA_DEPTH              = 2,
  localparam  int               INFO_WIDTH              = get_request_info_width(BUS_CONFIG, 1)
)(
  input   var                                 i_clk,
  input   var                                 i_rst_n,
  output  var                                 o_mcmd_done,
  output  var                                 o_mdata_done,
  output  var pzcorebus_command_type          o_mcmd,
  output  var [BUS_CONFIG.id_width-1:0]       o_mid,
  output  var [BUS_CONFIG.address_width-1:0]  o_maddr,
  output  var [INFO_WIDTH-1:0]                o_minfo,
  interface.request_slave                     slave_if,
  interface.request_master                    master_if
);
  localparam  bit STRICT_MODE = !RELAX_MODE;

//--------------------------------------------------------------
//  Slave IF FIFO
//--------------------------------------------------------------
  pzcorebus_request_if #(BUS_CONFIG)  fifo_if();

  pzcorebus_request_fifo #(
    .BUS_CONFIG     (BUS_CONFIG     ),
    .COMMAND_DEPTH  (COMMAND_DEPTH  ),
    .COMMAND_VALID  (SLAVE_FIFO     ),
    .DATA_DEPTH     (DATA_DEPTH     ),
    .DATA_VALID     (SLAVE_FIFO     )
  ) u_slave_fifo (
    .i_clk          (i_clk    ),
    .i_rst_n        (i_rst_n  ),
    .i_clear        ('0       ),
    .o_empty        (),
    .o_almost_full  (),
    .o_full         (),
    .slave_if       (slave_if ),
    .master_if      (fifo_if  )
  );

//--------------------------------------------------------------
//  State Machine
//--------------------------------------------------------------
  typedef enum logic [1:0] {
    IDLE,
    ACTIVE,
    DONE
  } pzcorebus_state;

  pzcorebus_state command_state;
  pzcorebus_state data_state;
  logic           commad_done;
  logic           data_done;

  always_comb begin
    o_mcmd_done   = command_state == DONE;
    o_mdata_done  = data_state == DONE;
  end

  always_comb begin
    commad_done = (command_state == DONE) || fifo_if.command_with_data_ack();
    data_done   = (data_state == DONE) || fifo_if.write_data_last_ack();
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      command_state <= IDLE;
    end
    else begin
      case (command_state)
        IDLE: begin
          if (commad_done && (!data_done)) begin
            command_state <= DONE;
          end
        end
        DONE: begin
          if (data_done) begin
            command_state <= IDLE;
          end
        end
      endcase
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      data_state  <= IDLE;
    end
    else begin
      case (data_state)
        IDLE: begin
          if (commad_done) begin
            if (!data_done) begin
              data_state  <= ACTIVE;
            end
          end
          else if (RELAX_MODE && fifo_if.command_with_data_valid()) begin
            if (data_done) begin
              data_state  <= DONE;
            end
            else if ((!WAIT_FOR_DATA) || fifo_if.mdata_valid) begin
              data_state  <= ACTIVE;
            end
          end
        end
        ACTIVE: begin
          if (data_done) begin
            if (STRICT_MODE || commad_done) begin
              data_state  <= IDLE;
            end
            else begin
              data_state  <= DONE;
            end
          end
        end
        DONE: begin
          if (commad_done) begin
            data_state  <= IDLE;
          end
        end
      endcase
    end
  end

//--------------------------------------------------------------
//  Master Port Connection
//--------------------------------------------------------------
  logic command_ready;
  logic data_ready;

  always_comb begin
    case (command_state)
      IDLE:     command_ready = (!WAIT_FOR_DATA) || fifo_if.is_command_no_data() || fifo_if.mdata_valid || (data_state != IDLE);
      default:  command_ready = THROUGH_NO_DATA_COMMAND && fifo_if.is_command_no_data();
    endcase

    case (data_state)
      IDLE:     data_ready  = (RELAX_MODE) ? fifo_if.command_with_data_valid() : fifo_if.command_with_data_ack();
      ACTIVE:   data_ready  = '1;
      default:  data_ready  = '0;
    endcase

    fifo_if.scmd_accept   = command_ready && master_if.scmd_accept;
    master_if.mcmd_valid  = command_ready && fifo_if.mcmd_valid;
    master_if.put_command(fifo_if.get_command());

    fifo_if.sdata_accept  = data_ready && master_if.sdata_accept;
    master_if.mdata_valid = data_ready && fifo_if.mdata_valid;
    master_if.put_write_data(fifo_if.get_write_data());
  end

//--------------------------------------------------------------
//  Request Info
//--------------------------------------------------------------
  pzcorebus_command_type                mcmd;
  logic [BUS_CONFIG.id_width-1:0]       mid;
  logic [BUS_CONFIG.address_width-1:0]  maddr;
  logic [INFO_WIDTH-1:0]                minfo;

  always_comb begin
    if (command_state == IDLE) begin
      o_mcmd  = fifo_if.mcmd;
      o_mid   = fifo_if.mid;
      o_maddr = fifo_if.maddr;
      o_minfo = fifo_if.minfo;
    end
    else begin
      o_mcmd  = mcmd;
      o_mid   = mid;
      o_maddr = maddr;
      o_minfo = minfo;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      mcmd  <= pzcorebus_command_type'(0);
      mid   <= '0;
      maddr <= '0;
      minfo <= '0;
    end
    else if (fifo_if.command_with_data_ack()) begin
      mcmd  <= fifo_if.mcmd;
      mid   <= fifo_if.mid;
      maddr <= fifo_if.maddr;
      minfo <= fifo_if.minfo;
    end
  end
endmodule
