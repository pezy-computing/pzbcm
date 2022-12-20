//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
package pzcorebus_if_pkg;
  import  pzcorebus_pkg::*;

  typedef struct {
    int lsb;
    int width;
  } pzcorebus_if_position_info;

  typedef struct {
    pzcorebus_if_position_info  mcmd;
    pzcorebus_if_position_info  mid;
    pzcorebus_if_position_info  maddr;
    pzcorebus_if_position_info  mlength;
    pzcorebus_if_position_info  minfo;
    pzcorebus_if_position_info  mdata;
  } pzcorebus_if_command_position_list;

  typedef struct {
    pzcorebus_if_position_info  mdata;
    pzcorebus_if_position_info  mdata_byteen;
    pzcorebus_if_position_info  mdata_last;
  } pzcorebus_if_write_data_position_list;

  typedef struct {
    pzcorebus_if_position_info  sresp;
    pzcorebus_if_position_info  sid;
    pzcorebus_if_position_info  serror;
    pzcorebus_if_position_info  sdata;
    pzcorebus_if_position_info  sinfo;
    pzcorebus_if_position_info  sresp_uniten;
    pzcorebus_if_position_info  sresp_last;
  } pzcorebus_if_response_position_list;

  function automatic int calc_next_lsb(pzcorebus_if_position_info info);
    return info.lsb + info.width;
  endfunction

  function automatic pzcorebus_if_command_position_list build_command_position_list(
    pzcorebus_config  bus_config
  );
    pzcorebus_if_command_position_list  list;

    list.mcmd.lsb       = 0;
    list.mcmd.width     = $bits(pzcorebus_command_type);
    list.mid.lsb        = calc_next_lsb(list.mcmd);
    list.mid.width      = bus_config.id_width;
    list.maddr.lsb      = calc_next_lsb(list.mid);
    list.maddr.width    = bus_config.address_width;
    list.mlength.lsb    = calc_next_lsb(list.maddr);
    list.mlength.width  = get_length_width(bus_config, 0);
    list.minfo.lsb      = calc_next_lsb(list.mlength);
    list.minfo.width    = get_request_info_width(bus_config, 0);
    list.mdata.lsb      = calc_next_lsb(list.minfo);
    if (bus_config.profile == PZCOREBUS_CSR) begin
      list.mdata.width  = bus_config.data_width;
    end
    else begin
      list.mdata.width  = 0;
    end

    return list;
  endfunction

  function automatic pzcorebus_if_write_data_position_list build_write_data_position_list(
    pzcorebus_config  bus_config
  );
    pzcorebus_if_write_data_position_list list;

    if (bus_config.profile != PZCOREBUS_CSR) begin
      list.mdata.lsb          = 0;
      list.mdata.width        = bus_config.data_width;
      list.mdata_byteen.lsb   = calc_next_lsb(list.mdata);
      list.mdata_byteen.width = get_byte_enable_width(bus_config, 0);
      list.mdata_last.lsb     = calc_next_lsb(list.mdata_byteen);
      list.mdata_last.width   = 1;
    end
    else begin
      list.mdata.lsb          = 0;
      list.mdata.width        = 0;
      list.mdata_byteen.lsb   = 0;
      list.mdata_byteen.width = 0;
      list.mdata_last.lsb     = 0;
      list.mdata_last.width   = 0;
    end

    return list;
  endfunction

  function automatic pzcorebus_if_response_position_list build_response_position_list(
    pzcorebus_config  bus_config
  );
    pzcorebus_if_response_position_list list;

    list.sresp.lsb          = 0;
    list.sresp.width        = $bits(pzcorebus_response_type);
    list.sid.lsb            = calc_next_lsb(list.sresp);
    list.sid.width          = bus_config.id_width;
    list.serror.lsb         = calc_next_lsb(list.sid);
    list.serror.width       = 1;
    list.sdata.lsb          = calc_next_lsb(list.serror);
    list.sdata.width        = bus_config.data_width;
    list.sinfo.lsb          = calc_next_lsb(list.sdata);
    list.sinfo.width        = get_response_info_width(bus_config, 0);
    list.sresp_uniten.lsb   = calc_next_lsb(list.sinfo);
    list.sresp_uniten.width = get_unit_enable_width(bus_config, 0);
    list.sresp_last.lsb     = calc_next_lsb(list.sresp_uniten);
    list.sresp_last.width   = get_response_last_width(bus_config, 0);

    return list;
  endfunction

  function automatic int get_command_packer_width(
    pzcorebus_if_command_position_list  list
  );
    int width = 0;
    width += list.mcmd.width;
    width += list.mid.width;
    width += list.maddr.width;
    width += list.mlength.width;
    width += list.minfo.width;
    width += list.mdata.width;
    width += 1;
    return width;
  endfunction

  function automatic int get_write_data_packer_width(
    pzcorebus_if_write_data_position_list list
  );
    int width = 0;
    width += list.mdata.width;
    width += list.mdata_byteen.width;
    width += list.mdata_last.width;
    width += 1;
    return width;
  endfunction

  function automatic int get_response_packer_width(
    pzcorebus_if_response_position_list list
  );
    int width = 0;
    width += list.sresp.width;
    width += list.sid.width;
    width += list.serror.width;
    width += list.sdata.width;
    width += list.sinfo.width;
    width += list.sresp_uniten.width;
    width += list.sresp_last.width;
    width += 1;
    return width;
  endfunction
endpackage
