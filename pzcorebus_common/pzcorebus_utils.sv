//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
interface pzcorebus_utils
  import  pzcorebus_pkg::*;
#(
  parameter pzcorebus_config  BUS_CONFIG  = '0
);
  `include  "pzcorebus_macros.svh"

  localparam  int DATA_SIZE     = BUS_CONFIG.data_width / BUS_CONFIG.unit_data_width;
  localparam  int MAX_DATA_SIZE = BUS_CONFIG.max_data_width / BUS_CONFIG.unit_data_width;

  function automatic int calc_width(int value);
    if (value >= 2) begin
      return $clog2(value);
    end
    else begin
      return 1;
    end
  endfunction

  typedef logic [BUS_CONFIG.address_width-1:0]                  pzcorebus_addrss;
  typedef logic [get_length_width(BUS_CONFIG, 1)-1:0]           pzcorebus_length;
  typedef logic [get_unpacked_length_width(BUS_CONFIG)-1:0]     pzcorebus_unpacked_length;
  typedef logic [get_burst_length_width(BUS_CONFIG)-1:0]        pzcorebus_burst_length;
  typedef logic [get_response_offset_width(BUS_CONFIG, 1)-1:0]  pzcorebus_response_offset;
  typedef logic [get_response_size_width(BUS_CONFIG)-1:0]       pzcorebus_response_size;
  typedef logic [get_unit_enable_width(BUS_CONFIG, 1)-1:0]      pzcorebus_unit_enable;

  function automatic logic is_non_posted_command(pzcorebus_command_type command_type);
    return command_type[PZCOREBUS_NON_POSTED_BIT];
  endfunction

  function automatic logic is_posted_command(pzcorebus_command_type command_type);
    return !command_type[PZCOREBUS_NON_POSTED_BIT];
  endfunction

  function automatic logic is_command_with_data(pzcorebus_command_type command_type);
    return command_type[PZCOREBUS_WITH_DATA_BIT];
  endfunction

  function automatic logic is_command_no_data(pzcorebus_command_type command_type);
    return !command_type[PZCOREBUS_WITH_DATA_BIT];
  endfunction

  function automatic logic is_read_command(pzcorebus_command_type command_type);
    return pzcorebus_command_kind'(command_type) == PZCOREBUS_READ_COMMAND;
  endfunction

  function automatic logic is_write_command(pzcorebus_command_type command_type);
    return pzcorebus_command_kind'(command_type) == PZCOREBUS_WRITE_COMMAND;
  endfunction

  function automatic logic is_full_write_command(pzcorebus_command_type command_type);
    if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin
      return pzcorebus_command_kind'(command_type) == PZCOREBUS_FULL_WRITE_COMMAND;
    end
    else begin
      return '0;
    end
  endfunction

  function automatic logic is_broadcast_command(pzcorebus_command_type command_type);
    if (`pzcorebus_csr_profile(BUS_CONFIG)) begin
      return pzcorebus_command_kind'(command_type) == PZCOREBUS_BROADCAST_COMMAND;
    end
    else begin
      return '0;
    end
  endfunction

  function automatic logic is_write_access_command(pzcorebus_command_type command_type);
    return is_write_command(command_type) || is_full_write_command(command_type) || is_broadcast_command(command_type);
  endfunction

  function automatic logic is_posted_write_acess_command(pzcorebus_command_type command_type);
    return is_posted_command(command_type) && is_write_access_command(command_type);
  endfunction

  function automatic logic is_non_posted_write_acess_command(pzcorebus_command_type command_type);
    return is_non_posted_command(command_type) && is_write_access_command(command_type);
  endfunction

  function automatic logic is_atomic_command(pzcorebus_command_type command_type);
    if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin
      return pzcorebus_command_kind'(command_type) == PZCOREBUS_ATOMIC_COMMAND;
    end
    else begin
      return '0;
    end
  endfunction

  function automatic logic is_message_command(pzcorebus_command_type command_type);
    if (`pzcorebus_memoy_profile(BUS_CONFIG)) begin
      return pzcorebus_command_kind'(command_type) == PZCOREBUS_MESSAGE_COMMAND;
    end
    else begin
      return '0;
    end
  endfunction

  function automatic logic is_response_with_data(pzcorebus_command_type command_type);
    return command_type inside {PZCOREBUS_READ, PZCOREBUS_ATOMIC_NON_POSTED};
  endfunction

  function automatic pzcorebus_length pack_length(pzcorebus_unpacked_length length);
    return pzcorebus_length'(length);
  endfunction

  function automatic pzcorebus_unpacked_length unpack_length(pzcorebus_length length);
    if (length != '0) begin
      return pzcorebus_unpacked_length'(length);
    end
    else begin
      return pzcorebus_unpacked_length'(BUS_CONFIG.max_length);
    end
  endfunction

  function automatic pzcorebus_unpacked_length get_length(
    pzcorebus_command_type  command_type,
    pzcorebus_length        length
  );
    case (1'b1)
      `pzcorebus_csr_profile(BUS_CONFIG): return pzcorebus_unpacked_length'(1);
      is_atomic_command(command_type):    return pzcorebus_unpacked_length'(DATA_SIZE);
      is_message_command(command_type):   return pzcorebus_unpacked_length'(0);
      default:                            return unpack_length(length);
    endcase
  endfunction

  localparam  int LENGTH_OFFSET_LSB   = $clog2(BUS_CONFIG.unit_data_width) - 3;
  localparam  int LENGTH_OFFSET_WIDTH = calc_width(DATA_SIZE);

  function automatic pzcorebus_unpacked_length get_aligned_length(
    pzcorebus_command_type  command_type,
    pzcorebus_addrss        address,
    pzcorebus_length        length
  );
    pzcorebus_unpacked_length offset;
    logic [3:0]               no_offset;

    no_offset[0]  = !`pzcorebus_memoy_h_profile(BUS_CONFIG);
    no_offset[1]  = DATA_SIZE == 1;
    no_offset[2]  = is_atomic_command(command_type);
    no_offset[3]  = is_message_command(command_type);
    if (no_offset != '1) begin
      offset  = pzcorebus_unpacked_length'(0);
    end
    else begin
      offset  = address[LENGTH_OFFSET_LSB+:LENGTH_OFFSET_WIDTH];
    end

    return get_length(command_type, length) + offset;
  endfunction

  localparam  int BURST_OFFSET  = DATA_SIZE - 1;
  localparam  int BURST_SHIFT   = $clog2(DATA_SIZE);

  function automatic pzcorebus_burst_length get_burst_length(
    pzcorebus_command_type  command_type,
    pzcorebus_addrss        address,
    pzcorebus_length        length
  );
    if (`pzcorebus_memoy_h_profile(BUS_CONFIG)) begin
      pzcorebus_unpacked_length length;
      length  = get_aligned_length(command_type, address, length)
              + pzcorebus_unpacked_length'(BURST_OFFSET);
      return pzcorebus_burst_length'(length >> BURST_SHIFT);
    end
    else begin
      return get_length(command_type, length);
    end
  endfunction

  function automatic pzcorebus_response_type get_sresp(pzcorebus_command_type command);
    if (is_response_with_data(command)) begin
      return PZCOREBUS_RESPONSE_WITH_DATA;
    end
    else begin
      return PZCOREBUS_RESPONSE;
    end
  endfunction

  function automatic pzcorebus_unpacked_length get_response_length(
    pzcorebus_command_type  command_type,
    pzcorebus_length        length
  );
    if (is_posted_command(command_type)) begin
      return pzcorebus_unpacked_length'(0);
    end
    else if (is_read_command(command_type)) begin
      return unpack_length(length);
    end
    else begin
      return pzcorebus_unpacked_length'(DATA_SIZE);
    end
  endfunction

  function automatic pzcorebus_burst_length get_burst_index(
    pzcorebus_length  index
  );
    if (`pzcorebus_memoy_h_profile(BUS_CONFIG)) begin
      return pzcorebus_burst_length'(index >> BURST_SHIFT);
    end
    else begin
      return index;
    end
  endfunction

  localparam  int RESPONSE_OFFSET_LSB   = $clog2(BUS_CONFIG.unit_data_width) - 3;
  localparam  int RESPONSE_OFFSET_WIDTH = calc_width(MAX_DATA_SIZE);

  function automatic pzcorebus_response_offset get_initial_offset(
    pzcorebus_command_type  command,
    pzcorebus_addrss        address
  );
    if (!`pzcorebus_memoy_h_profile(BUS_CONFIG)) begin
      return pzcorebus_response_offset'(0);
    end
    else if (BUS_CONFIG.max_data_width == BUS_CONFIG.unit_data_width) begin
      return pzcorebus_response_offset'(0);
    end
    else if (command != PZCOREBUS_READ) begin
      return pzcorebus_response_offset'(0);
    end
    else begin
      return address[RESPONSE_OFFSET_LSB+:RESPONSE_OFFSET_WIDTH];
    end
  endfunction

  localparam  pzcorebus_response_offset OFFSET_MASK = DATA_SIZE - 1;

  function automatic pzcorebus_response_offset get_next_offset(
    pzcorebus_response_offset current_offset
  );
    return (current_offset & (~OFFSET_MASK)) + pzcorebus_response_offset'(DATA_SIZE);
  endfunction

  localparam  int RESPONSE_OFFSET_SLICE_WIDTH = calc_width(DATA_SIZE);

  function automatic pzcorebus_response_size calc_response_size(
    pzcorebus_unpacked_length remaining_size,
    pzcorebus_response_offset current_offset
  );
    if (!`pzcorebus_memoy_h_profile(BUS_CONFIG)) begin
      return pzcorebus_response_size'(1);
    end
    else if (BUS_CONFIG.data_width == BUS_CONFIG.unit_data_width) begin
      return pzcorebus_response_size'(1);
    end
    else begin
      pzcorebus_response_size offset;
      pzcorebus_response_size size;

      offset  = pzcorebus_response_size'(current_offset[0+:RESPONSE_OFFSET_SLICE_WIDTH]);
      size    = pzcorebus_response_size'(DATA_SIZE) - offset;
      if (size < remaining_size) begin
        return size;
      end
      else begin
        return pzcorebus_response_size'(remaining_size);
      end
    end
  endfunction

  function automatic pzcorebus_unit_enable get_sresp_uniten(
    pzcorebus_response_offset current_offset,
    pzcorebus_response_size   response_size
  );
    if (!`pzcorebus_memoy_h_profile(BUS_CONFIG)) begin
      return '0;
    end
    else begin
      pzcorebus_unit_enable unit_enable;

      for (int i = 0;i < $bits(pzcorebus_response_size);++i) begin
        if ((i >= current_offset) && (i < (current_offset + response_size))) begin
          unit_enable[i]  = '1;
        end
        else begin
          unit_enable[i]  = '0;
        end
      end

      return unit_enable;
    end
  endfunction
endinterface
