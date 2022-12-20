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
  localparam  int DATA_SIZE = BUS_CONFIG.data_width / BUS_CONFIG.unit_data_width;

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

  function automatic logic is_atomic_command(pzcorebus_command_type command_type);
    return command_type[1:0] == 2'b10;
  endfunction

  function automatic logic is_message_command(pzcorebus_command_type command_type);
    return command_type[1:0] == 2'b11;
  endfunction

  function automatic logic is_response_with_data(pzcorebus_command_type command_type);
    return command_type inside {PZCOREBUS_READ, PZCOREBUS_ATOMIC_NON_POSTED};
  endfunction

  function automatic pzcorebus_length pack_length(pzcorebus_unpacked_length length);
    return pzcorebus_length'(length);
  endfunction

  localparam  pzcorebus_unpacked_length MAX_LENGTH  = BUS_CONFIG.max_length;

  function automatic pzcorebus_unpacked_length unpack_length(pzcorebus_length length);
    if (BUS_CONFIG.profile == PZCOREBUS_CSR) begin
      return pzcorebus_unpacked_length'(1);
    end
    else if (length != '0) begin
      return pzcorebus_unpacked_length'(length);
    end
    else begin
      return MAX_LENGTH;
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

  localparam  int LENGTH_OFFSET_LSB   = $clog2(BUS_CONFIG.unit_data_width) - 3;
  localparam  int LENGTH_OFFSET_WIDTH = (DATA_SIZE > 1) ? $clog2(DATA_SIZE) : 1;

  function automatic pzcorebus_unpacked_length get_length_offset(
    pzcorebus_command_type  command,
    pzcorebus_addrss        address
  );
    if (BUS_CONFIG.profile != PZCOREBUS_MEMORY_H) begin
      return pzcorebus_unpacked_length'(0);
    end
    else if (DATA_SIZE == 1) begin
      return pzcorebus_unpacked_length'(0);
    end
    if (is_message_command(command)) begin
      return pzcorebus_unpacked_length'(0);
    end
    else if (is_atomic_command(command)) begin
      return pzcorebus_unpacked_length'(0);
    end
    else begin
      return pzcorebus_unpacked_length'(address[LENGTH_OFFSET_LSB+:LENGTH_OFFSET_WIDTH]);
    end
  endfunction

  function automatic pzcorebus_unpacked_length get_aligned_length(
    pzcorebus_command_type  command,
    pzcorebus_addrss        address,
    pzcorebus_length        length
  );
    if (is_message_command(command)) begin
      return pzcorebus_unpacked_length'(DATA_SIZE);
    end
    else begin
      return unpack_length(length) + get_length_offset(command, address);
    end
  endfunction

  localparam  int BURST_LSB     = $clog2(BUS_CONFIG.data_width / BUS_CONFIG.unit_data_width);
  localparam  int BURST_OFFSET  = (BUS_CONFIG.data_width / BUS_CONFIG.unit_data_width) - 1;

  function automatic pzcorebus_burst_length get_burst_length(
    pzcorebus_command_type  command,
    pzcorebus_addrss        address,
    pzcorebus_length        length
  );
    if (BUS_CONFIG.profile == PZCOREBUS_MEMORY_H) begin
      pzcorebus_unpacked_length temp;
      temp  = get_aligned_length(command, address, length)
            + pzcorebus_unpacked_length'(BURST_OFFSET);
      return temp[$bits(pzcorebus_unpacked_length)-1:BURST_LSB];
    end
    else begin
      return unpack_length(length);
    end
  endfunction

  function automatic pzcorebus_burst_length get_burst_index(
    pzcorebus_length  index
  );
    if (BUS_CONFIG.profile == PZCOREBUS_MEMORY_H) begin
      return index[$bits(pzcorebus_length)-1:BURST_LSB];
    end
    else begin
      return index;
    end
  endfunction

  localparam  int RESPONSE_OFFSET_LSB   = $clog2(BUS_CONFIG.unit_data_width) - 3;
  localparam  int RESPONSE_OFFSET_WIDTH =
    (BUS_CONFIG.max_data_width > BUS_CONFIG.unit_data_width) ?
      $clog2(BUS_CONFIG.max_data_width / BUS_CONFIG.unit_data_width) : 1;

  function automatic pzcorebus_response_offset get_initial_offset(
    pzcorebus_command_type  command,
    pzcorebus_addrss        address
  );
    if (BUS_CONFIG.profile != PZCOREBUS_MEMORY_H) begin
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

  localparam  int RESPONSE_OFFSET_SLICE_WIDTH =
    (BUS_CONFIG.data_width > BUS_CONFIG.unit_data_width) ?
      $clog2(BUS_CONFIG.data_width / BUS_CONFIG.unit_data_width) : 1;

  function automatic pzcorebus_response_size calc_response_size(
    pzcorebus_unpacked_length remaining_size,
    pzcorebus_response_offset current_offset
  );
    if (BUS_CONFIG.profile != PZCOREBUS_MEMORY_H) begin
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
    if (BUS_CONFIG.profile != PZCOREBUS_MEMORY_H) begin
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

  modport utils(
    import  is_non_posted_command,
    import  is_posted_command,
    import  is_command_with_data,
    import  is_command_no_data,
    import  is_atomic_command,
    import  is_message_command,
    import  is_response_with_data,
    import  pack_length,
    import  unpack_length,
    import  get_sresp,
    import  get_length_offset,
    import  get_aligned_length,
    import  get_burst_length,
    import  get_burst_index,
    import  get_initial_offset,
    import  get_next_offset,
    import  calc_response_size,
    import  get_sresp_uniten
  );
endinterface
