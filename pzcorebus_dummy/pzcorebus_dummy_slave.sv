//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
module pzcorebus_dummy_slave
  import  pzcorebus_pkg::*,
          pzcorebus_dummy_pkg::*;
#(
  parameter pzcorebus_config                BUS_CONFIG      = '0,
  parameter bit                             TIE_OFF         = 0,
  parameter bit                             ERROR           = '1,
  parameter bit [31:0]                      ERROR_DATA      = get_error_data(BUS_CONFIG),
  parameter bit [BUS_CONFIG.data_width-1:0] READ_DATA       = {BUS_CONFIG.data_width/32{ERROR_DATA}},
  parameter bit                             ENABLE_WARNING  = 1
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if
);
  typedef logic [BUS_CONFIG.id_width-1:0]                       pzcorebus_id;
  typedef logic [BUS_CONFIG.address_width-1:0]                  pzcorebus_addrss;
  typedef logic [get_length_width(BUS_CONFIG, 1)-1:0]           pzcorebus_length;
  typedef logic [get_unpacked_length_width(BUS_CONFIG)-1:0]     pzcorebus_unpacked_length;
  typedef logic [get_unit_enable_width(BUS_CONFIG, 1)-1:0]      pzcorebus_unit_enable;
  typedef logic [get_response_last_width(BUS_CONFIG, 1)-1:0]    pzcorebus_response_last;
  typedef logic [get_response_offset_width(BUS_CONFIG, 1)-1:0]  pzcorebus_response_offset;
  typedef logic [get_response_size_width(BUS_CONFIG)-1:0]       pzcorebus_response_size;

  localparam  int DATA_SIZE     = BUS_CONFIG.data_size;
  localparam  int OFFSET_LSB    = get_response_offset_lsb(BUS_CONFIG);
  localparam  int OFFSET_WIDTH  = (DATA_SIZE > 1) ? $clog2(DATA_SIZE) : 1;

  if (TIE_OFF) begin : g
    always_comb begin
      slave_if.scmd_accept  = '1;
      slave_if.sdata_accept = '1;
      slave_if.sresp_valid  = '0;
      slave_if.sresp        = pzcorebus_response_type'(0);
      slave_if.sid          = '0;
      slave_if.serror       = '0;
      slave_if.sdata        = '0;
      slave_if.sinfo        = '0;
      slave_if.sresp_uniten = '0;
      slave_if.sresp_last   = '0;
    end
  end
  else begin : g
    pzcorebus_if #(BUS_CONFIG)  corebus_if();
    logic                       scmd_accept;
    logic                       sdata_accept;
    logic [1:0]                 sresp_valid;
    pzcorebus_response_type     sresp;
    pzcorebus_id                sid;
    logic                       serror;
    pzcorebus_unit_enable       sresp_uniten;
    pzcorebus_response_last     sresp_last;

    pzcorebus_slicer #(
      .BUS_CONFIG     (BUS_CONFIG                           ),
      .FIFO_SLICER    (`pzcorebus_memoy_profile(BUS_CONFIG) ),
      .REQUEST_VALID  (0                                    ),
      .RESPONSE_VALID (1                                    )
    ) u_slicer (
      .i_clk      (i_clk      ),
      .i_rst_n    (i_rst_n    ),
      .slave_if   (slave_if   ),
      .master_if  (corebus_if )
    );

    always_comb begin
      corebus_if.scmd_accept  = scmd_accept;
      corebus_if.sdata_accept = sdata_accept;
      corebus_if.sresp_valid  = sresp_valid == '1;
      corebus_if.sresp        = sresp;
      corebus_if.sid          = sid;
      corebus_if.serror       = serror;
      corebus_if.sdata        = READ_DATA;
      corebus_if.sinfo        = '0;
      corebus_if.sresp_uniten = sresp_uniten;
      corebus_if.sresp_last   = sresp_last;
    end

    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (!i_rst_n) begin
        sresp   <= pzcorebus_response_type'(0);
        sid     <= '0;
        serror  <= '0;
      end
      else if (corebus_if.command_non_posted_ack()) begin
        sresp <= get_sresp(corebus_if.mcmd);
        sid   <= corebus_if.mid;
        if (corebus_if.is_broadcast_command()) begin
          serror  <= '0;
        end
        else begin
          serror  <= ERROR;
        end
      end
    end

    if (is_csr_profile(BUS_CONFIG)) begin : g_csrbus
      always_comb begin
        scmd_accept     = !sresp_valid[0];
        sdata_accept    = '0;
        sresp_valid[1]  = '1;
        sresp_uniten    = '0;
        sresp_last      = '0;
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          sresp_valid[0]  <= '0;
        end
        else if (corebus_if.response_last_ack()) begin
          sresp_valid[0]  <= '0;
        end
        else if (corebus_if.command_non_posted_ack()) begin
          sresp_valid[0]  <= '1;
        end
      end
    end
    else begin : g_membus
      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          scmd_accept <= '1;
        end
        else if (corebus_if.response_last_ack()) begin
          scmd_accept <= '1;
        end
        else if (corebus_if.write_data_last_ack()) begin
          scmd_accept <= !sresp_valid[0];
        end
        else if (corebus_if.command_ack()) begin
          if (corebus_if.mcmd != PZCOREBUS_MESSAGE) begin
            scmd_accept <= '0;
          end
        end
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          sdata_accept  <= '0;
        end
        else if (corebus_if.write_data_last_ack()) begin
          sdata_accept  <= '0;
        end
        else if (corebus_if.command_with_data_ack()) begin
          sdata_accept  <= '1;
        end
      end

      always_ff @(posedge i_clk, negedge i_rst_n) begin
        if (!i_rst_n) begin
          sresp_valid[0]  <= '0;
          sresp_valid[1]  <= '0;
        end
        else if (corebus_if.response_last_ack()) begin
          sresp_valid[0]  <= '0;
          sresp_valid[1]  <= '0;
        end
        else if (corebus_if.command_non_posted_ack()) begin
          sresp_valid[0]  <= '1;
          sresp_valid[1]  <= corebus_if.is_command_with_response_data();
        end
        else if (corebus_if.write_data_last_ack()) begin
          sresp_valid[1]  <= sresp_valid[0];
        end
      end

      if (is_memory_l_profile(BUS_CONFIG)) begin : g_membus_l
        pzcorebus_unpacked_length sresp_count;

        always_comb begin
          sresp_uniten  = '0;
          sresp_last    = sresp_count == pzcorebus_unpacked_length'(1);
        end

        always_ff @(posedge i_clk, negedge i_rst_n) begin
          if (!i_rst_n) begin
            sresp_count <= pzcorebus_unpacked_length'(0);
          end
          else if (corebus_if.command_non_posted_ack()) begin
            sresp_count <= corebus_if.get_response_length();
          end
          else if (corebus_if.response_ack()) begin
            sresp_count <= sresp_count - pzcorebus_unpacked_length'(1);
          end
        end
      end
      else begin : g_membus_h
        pzcorebus_unpacked_length mlength;
        pzcorebus_response_size   sresp_size;
        pzcorebus_unpacked_length sresp_count;
        pzcorebus_unpacked_length sresp_count_next;
        pzcorebus_response_offset sresp_offset;
        pzcorebus_response_offset sresp_offset_next;

        always_comb begin
          sresp_uniten  = get_sresp_uniten(sresp_offset, sresp_size);
          sresp_last    = (sresp_count_next >= mlength) ? '1 : '0;
        end

        always_comb begin
          sresp_size        = get_sresp_size(mlength, sresp_count, sresp_offset);
          sresp_count_next  = sresp_count  + pzcorebus_unpacked_length'(sresp_size);
          sresp_offset_next = sresp_offset + pzcorebus_response_offset'(sresp_size);
        end

        always_ff @(posedge i_clk, negedge i_rst_n) begin
          if (!i_rst_n) begin
            mlength <= pzcorebus_unpacked_length'(0);
          end
          else if (corebus_if.command_non_posted_ack()) begin
            mlength <= corebus_if.get_response_length();
          end
        end

        always_ff @(posedge i_clk, negedge i_rst_n) begin
          if (!i_rst_n) begin
            sresp_count   <= pzcorebus_unpacked_length'(0);
            sresp_offset  <= pzcorebus_response_offset'(0);
          end
          else if (corebus_if.command_non_posted_ack()) begin
            sresp_count <= pzcorebus_unpacked_length'(0);
            if (corebus_if.is_read_command()) begin
              sresp_offset  <= pzcorebus_response_offset'(corebus_if.maddr >> OFFSET_LSB);
            end
            else begin
              sresp_offset  <= pzcorebus_response_offset'(0);
            end
          end
          else if (corebus_if.response_ack()) begin
            sresp_count   <= sresp_count_next;
            sresp_offset  <= sresp_offset_next;
          end
        end
      end
    end
  end

  function automatic pzcorebus_response_type get_sresp(
    pzcorebus_command_type  mcmd
  );
    case (pzcorebus_command_kind'(mcmd))
      PZCOREBUS_READ_COMMAND:   return PZCOREBUS_RESPONSE_WITH_DATA;
      PZCOREBUS_ATOMIC_COMMAND: return PZCOREBUS_RESPONSE_WITH_DATA;
      default:                  return PZCOREBUS_RESPONSE;
    endcase
  endfunction

  function automatic pzcorebus_response_size get_sresp_size(
    pzcorebus_unpacked_length mlength,
    pzcorebus_unpacked_length sresp_count,
    pzcorebus_response_offset sresp_offset
  );
    logic [OFFSET_WIDTH-1:0]  offset;
    pzcorebus_unpacked_length size[2];

    offset  = OFFSET_WIDTH'(sresp_offset);
    size[0] = pzcorebus_unpacked_length'(DATA_SIZE) - pzcorebus_unpacked_length'(offset);
    size[1] = mlength - sresp_count;

    if (size[0] < size[1]) begin
      return pzcorebus_response_size'(size[0]);
    end
    else begin
      return pzcorebus_response_size'(size[1]);
    end
  endfunction

  function automatic pzcorebus_unit_enable get_sresp_uniten(
    pzcorebus_unpacked_length sresp_offset,
    pzcorebus_response_offset sresp_size
  );
    pzcorebus_response_offset start_index;
    pzcorebus_response_offset end_index;
    pzcorebus_unit_enable     uniten;

    start_index = sresp_offset;
    end_index   = start_index + pzcorebus_response_offset'(sresp_size) - pzcorebus_response_offset'(1);
    for (int i = 0;i < $bits(pzcorebus_unit_enable);++i) begin
      uniten[i] = i inside {[start_index:end_index]};
    end

    return uniten;
  endfunction

`ifndef SYNTHESIS
  `ifdef _PZ_UVM_
  import  uvm_pkg::*;
  `include  "uvm_macros.svh"
  function automatic void print_warning(string id, string message);
    `uvm_warning(id, message)
  endfunction
  `else
  function automatic void print_warning(string id, string message);
    $warning(message);
  endfunction
  `endif

  property p_no_requests_arrive;
    @(posedge i_clk) disable iff (!i_rst_n)
    !(slave_if.mcmd_valid && (!slave_if.is_broadcast_command()));
  endproperty

  if (ENABLE_WARNING) begin : g_sva
    ast_no_requests_arrive:
    assert property(p_no_requests_arrive)
    else
      print_warning(
        "SLAVEDUMMY",
        $sformatf(
          "unexpected request arrives: mcmd %s mid %0h maddr %h path %m",
          slave_if.mcmd, slave_if.mid, slave_if.maddr
        )
      );
  end
`endif
endmodule

module pzcorebus_array_dummy_slave
  import  pzcorebus_pkg::*,
          pzcorebus_dummy_pkg::*;
#(
  parameter pzcorebus_config                BUS_CONFIG      = '0,
  parameter int                             SLAVES          = 2,
  parameter bit                             TIE_OFF         = 0,
  parameter bit                             ERROR           = '1,
  parameter bit [31:0]                      ERROR_DATA      = get_error_data(BUS_CONFIG),
  parameter bit [BUS_CONFIG.data_width-1:0] READ_DATA       = {BUS_CONFIG.data_width/32{ERROR_DATA}},
  parameter bit                             ENABLE_WARNING  = 1
)(
  input var           i_clk,
  input var           i_rst_n,
  pzcorebus_if.slave  slave_if[SLAVES]
);
  for (genvar i = 0;i < SLAVES;++i) begin : g
    pzcorebus_dummy_slave #(
      .BUS_CONFIG     (BUS_CONFIG     ),
      .TIE_OFF        (TIE_OFF        ),
      .ERROR          (ERROR          ),
      .ERROR_DATA     (ERROR_DATA     ),
      .READ_DATA      (READ_DATA      ),
      .ENABLE_WARNING (ENABLE_WARNING )
    ) u_dummy (
      .i_clk    (i_clk        ),
      .i_rst_n  (i_rst_n      ),
      .slave_if (slave_if[i]  )
    );
  end
endmodule
