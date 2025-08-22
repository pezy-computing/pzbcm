//========================================
//
// Copyright (c) 2022 PEZY Computing, K.K.
//
//========================================
`ifndef INCLUDED_PZCOREBUS_MACROS_SVH
`define INCLUDED_PZCOREBUS_MACROS_SVH

//----------------------------------------------------------
//  Utilities
//----------------------------------------------------------
`define pzcorebus_csr_profile(BUS_CONFIG) (BUS_CONFIG.profile == pzcorebus_pkg::PZCOREBUS_CSR)

`define pzcorebus_memoy_h_profile(BUS_CONFIG) (BUS_CONFIG.profile == pzcorebus_pkg::PZCOREBUS_MEMORY_H)

`define pzcorebus_memoy_l_profile(BUS_CONFIG) (BUS_CONFIG.profile == pzcorebus_pkg::PZCOREBUS_MEMORY_L)

`define pzcorebus_memoy_profile(BUS_CONFIG) (!`pzcorebus_csr_profile(BUS_CONFIG))

//----------------------------------------------------------
//  CSR bus slave
//----------------------------------------------------------
`define pzcorebus_define_csrbus_slave_ports(PREFIX, IF_CONFIG, N) \
input   var [N-1:0]                                                           i_``PREFIX``_mcmd_valid, \
output  var [N-1:0]                                                           o_``PREFIX``_scmd_accept, \
input   var [N-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]   i_``PREFIX``_mcmd, \
output  var [N-1:0]                                                           o_``PREFIX``_sresp_valid, \
input   var [N-1:0]                                                           i_``PREFIX``_mresp_accept, \
output  var [N-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]  o_``PREFIX``_sresp

`define pzcorebus_unpack_csrbus_slave_if(PREFIX, IF_NAME, IF_CONFIG, N) \
pzcorebus_array_if_unpacker #( \
  .BUS_CONFIG (IF_CONFIG  ), \
  .SIZE       (N          ) \
) u_``PREFIX``_unpacker ( \
  .corebus_if     (IF_NAME                    ), \
  .i_mcmd_valid   (i_``PREFIX``_mcmd_valid    ), \
  .o_scmd_accept  (o_``PREFIX``_scmd_accept   ), \
  .i_mcmd         (i_``PREFIX``_mcmd          ), \
  .i_mdata_valid  ('0                         ), \
  .o_sdata_accept (), \
  .i_mdata        ('0                         ), \
  .o_sresp_valid  (o_``PREFIX``_sresp_valid   ), \
  .i_mresp_accept (i_``PREFIX``_mresp_accept  ), \
  .o_sresp        (o_``PREFIX``_sresp         ) \
);

`define pzcorebus_pack_csrbus_slave_if(PREFIX, IF_NAME, IF_CONFIG, N) \
logic [N-1:0]                                                           PREFIX``_mcmd_valid; \
logic [N-1:0]                                                           PREFIX``_scmd_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]   PREFIX``_mcmd; \
logic [N-1:0]                                                           PREFIX``_sresp_valid; \
logic [N-1:0]                                                           PREFIX``_mresp_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]  PREFIX``_sresp; \
pzcorebus_array_if_packer #( \
  .BUS_CONFIG (IF_CONFIG  ), \
  .SIZE       (N          ) \
) u_``PREFIX``_packer ( \
  .corebus_if     (IF_NAME                ), \
  .o_mcmd_valid   (PREFIX``_mcmd_valid    ), \
  .i_scmd_accept  (PREFIX``_scmd_accept   ), \
  .o_mcmd         (PREFIX``_mcmd          ), \
  .o_mdata_valid  (), \
  .i_sdata_accept ('0                     ), \
  .o_mdata        (), \
  .i_sresp_valid  (PREFIX``_sresp_valid   ), \
  .o_mresp_accept (PREFIX``_mresp_accept  ), \
  .i_sresp        (PREFIX``_sresp         ) \
);

`define pzcorebus_connect_csrbus_slave_ports(PREFIX) \
.i_``PREFIX``_mcmd_valid    (PREFIX``_mcmd_valid    ), \
.o_``PREFIX``_scmd_accept   (PREFIX``_scmd_accept   ), \
.i_``PREFIX``_mcmd          (PREFIX``_mcmd          ), \
.o_``PREFIX``_sresp_valid   (PREFIX``_sresp_valid   ), \
.i_``PREFIX``_mresp_accept  (PREFIX``_mresp_accept  ), \
.o_``PREFIX``_sresp         (PREFIX``_sresp         )

//----------------------------------------------------------
//  CSR bus master
//----------------------------------------------------------
`define pzcorebus_define_csrbus_master_ports(PREFIX, IF_CONFIG, N) \
output  var [N-1:0]                                                           o_``PREFIX``_mcmd_valid, \
input   var [N-1:0]                                                           i_``PREFIX``_scmd_accept, \
output  var [N-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]   o_``PREFIX``_mcmd, \
input   var [N-1:0]                                                           i_``PREFIX``_sresp_valid, \
output  var [N-1:0]                                                           o_``PREFIX``_mresp_accept, \
input   var [N-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]  i_``PREFIX``_sresp

`define pzcorebus_pack_csrbus_master_if(PREFIX, IF_NAME, IF_CONFIG, N) \
pzcorebus_array_if_packer #( \
  .BUS_CONFIG (IF_CONFIG  ), \
  .SIZE       (N          ) \
) u_``PREFIX``_packer ( \
  .corebus_if     (IF_NAME                    ), \
  .o_mcmd_valid   (o_``PREFIX``_mcmd_valid    ), \
  .i_scmd_accept  (i_``PREFIX``_scmd_accept   ), \
  .o_mcmd         (o_``PREFIX``_mcmd          ), \
  .o_mdata_valid  (), \
  .i_sdata_accept ('0                         ), \
  .o_mdata        (), \
  .i_sresp_valid  (i_``PREFIX``_sresp_valid   ), \
  .o_mresp_accept (o_``PREFIX``_mresp_accept  ), \
  .i_sresp        (i_``PREFIX``_sresp         ) \
);

`define pzcorebus_unpack_csrbus_master_if(PREFIX, IF_NAME, IF_CONFIG, N) \
logic [N-1:0]                                                           PREFIX``_mcmd_valid; \
logic [N-1:0]                                                           PREFIX``_scmd_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]   PREFIX``_mcmd; \
logic [N-1:0]                                                           PREFIX``_sresp_valid; \
logic [N-1:0]                                                           PREFIX``_mresp_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]  PREFIX``_sresp; \
pzcorebus_array_if_unpacker #( \
  .BUS_CONFIG (IF_CONFIG  ), \
  .SIZE       (N          ) \
) u_``PREFIX``_unpacker ( \
  .corebus_if     (IF_NAME                ), \
  .i_mcmd_valid   (PREFIX``_mcmd_valid    ), \
  .o_scmd_accept  (PREFIX``_scmd_accept   ), \
  .i_mcmd         (PREFIX``_mcmd          ), \
  .i_mdata_valid  ('0                     ), \
  .o_sdata_accept (), \
  .i_mdata        ('0                     ), \
  .o_sresp_valid  (PREFIX``_sresp_valid   ), \
  .i_mresp_accept (PREFIX``_mresp_accept  ), \
  .o_sresp        (PREFIX``_sresp         ) \
);

`define pzcorebus_connect_csrbus_master_ports(PREFIX) \
.o_``PREFIX``_mcmd_valid    (PREFIX``_mcmd_valid    ), \
.i_``PREFIX``_scmd_accept   (PREFIX``_scmd_accept   ), \
.o_``PREFIX``_mcmd          (PREFIX``_mcmd          ), \
.i_``PREFIX``_sresp_valid   (PREFIX``_sresp_valid   ), \
.o_``PREFIX``_mresp_accept  (PREFIX``_mresp_accept  ), \
.i_``PREFIX``_sresp         (PREFIX``_sresp         )

//----------------------------------------------------------
//  Memory bus slave
//----------------------------------------------------------
`define pzcorebus_define_membus_slave_ports(PREFIX, IF_CONFIG, N) \
input   var [N-1:0]                                                                 i_``PREFIX``_mcmd_valid, \
output  var [N-1:0]                                                                 o_``PREFIX``_scmd_accept, \
input   var [N-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]         i_``PREFIX``_mcmd, \
input   var [N-1:0]                                                                 i_``PREFIX``_mdata_valid, \
output  var [N-1:0]                                                                 o_``PREFIX``_sdata_accept, \
input   var [N-1:0][pzcorebus_pkg::get_packed_write_data_width(IF_CONFIG, 1)-1:0]   i_``PREFIX``_mdata, \
output  var [N-1:0]                                                                 o_``PREFIX``_sresp_valid, \
input   var [N-1:0]                                                                 i_``PREFIX``_mresp_accept, \
output  var [N-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]        o_``PREFIX``_sresp

`define pzcorebus_unpack_membus_slave_if(PREFIX, IF_NAME, IF_CONFIG, N) \
pzcorebus_array_if_unpacker #( \
  .BUS_CONFIG (IF_CONFIG  ), \
  .SIZE       (N          ) \
) u_``PREFIX``_unpacker ( \
  .corebus_if     (IF_NAME                    ), \
  .i_mcmd_valid   (i_``PREFIX``_mcmd_valid    ), \
  .o_scmd_accept  (o_``PREFIX``_scmd_accept   ), \
  .i_mcmd         (i_``PREFIX``_mcmd          ), \
  .i_mdata_valid  (i_``PREFIX``_mdata_valid   ), \
  .o_sdata_accept (o_``PREFIX``_sdata_accept  ), \
  .i_mdata        (i_``PREFIX``_mdata         ), \
  .o_sresp_valid  (o_``PREFIX``_sresp_valid   ), \
  .i_mresp_accept (i_``PREFIX``_mresp_accept  ), \
  .o_sresp        (o_``PREFIX``_sresp         ) \
);

`define pzcorebus_pack_membus_slave_if(PREFIX, IF_NAME, IF_CONFIG, N) \
logic [N-1:0]                                                                 PREFIX``_mcmd_valid; \
logic [N-1:0]                                                                 PREFIX``_scmd_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]         PREFIX``_mcmd; \
logic [N-1:0]                                                                 PREFIX``_mdata_valid; \
logic [N-1:0]                                                                 PREFIX``_sdata_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_write_data_width(IF_CONFIG, 1)-1:0]   PREFIX``_mdata; \
logic [N-1:0]                                                                 PREFIX``_sresp_valid; \
logic [N-1:0]                                                                 PREFIX``_mresp_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]        PREFIX``_sresp; \
pzcorebus_array_if_packer #( \
  .BUS_CONFIG (IF_CONFIG  ), \
  .SIZE       (N          ) \
) u_``PREFIX``_packer ( \
  .corebus_if     (IF_NAME                ), \
  .o_mcmd_valid   (PREFIX``_mcmd_valid    ), \
  .i_scmd_accept  (PREFIX``_scmd_accept   ), \
  .o_mcmd         (PREFIX``_mcmd          ), \
  .o_mdata_valid  (PREFIX``_mdata_valid   ), \
  .i_sdata_accept (PREFIX``_sdata_accept  ), \
  .o_mdata        (PREFIX``_mdata         ), \
  .i_sresp_valid  (PREFIX``_sresp_valid   ), \
  .o_mresp_accept (PREFIX``_mresp_accept  ), \
  .i_sresp        (PREFIX``_sresp         ) \
);

`define pzcorebus_connect_membus_slave_ports(PREFIX) \
.i_``PREFIX``_mcmd_valid    (PREFIX``_mcmd_valid    ), \
.o_``PREFIX``_scmd_accept   (PREFIX``_scmd_accept   ), \
.i_``PREFIX``_mcmd          (PREFIX``_mcmd          ), \
.i_``PREFIX``_mdata_valid   (PREFIX``_mdata_valid   ), \
.o_``PREFIX``_sdata_accept  (PREFIX``_sdata_accept  ), \
.i_``PREFIX``_mdata         (PREFIX``_mdata         ), \
.o_``PREFIX``_sresp_valid   (PREFIX``_sresp_valid   ), \
.i_``PREFIX``_mresp_accept  (PREFIX``_mresp_accept  ), \
.o_``PREFIX``_sresp         (PREFIX``_sresp         )

//----------------------------------------------------------
//  Memory bus master
//----------------------------------------------------------
`define pzcorebus_define_membus_master_ports(PREFIX, IF_CONFIG, N) \
output  var [N-1:0]                                                                 o_``PREFIX``_mcmd_valid, \
input   var [N-1:0]                                                                 i_``PREFIX``_scmd_accept, \
output  var [N-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]         o_``PREFIX``_mcmd, \
output  var [N-1:0]                                                                 o_``PREFIX``_mdata_valid, \
input   var [N-1:0]                                                                 i_``PREFIX``_sdata_accept, \
output  var [N-1:0][pzcorebus_pkg::get_packed_write_data_width(IF_CONFIG, 1)-1:0]   o_``PREFIX``_mdata, \
input   var [N-1:0]                                                                 i_``PREFIX``_sresp_valid, \
output  var [N-1:0]                                                                 o_``PREFIX``_mresp_accept, \
input   var [N-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]        i_``PREFIX``_sresp

`define pzcorebus_pack_membus_master_if(PREFIX, IF_NAME, IF_CONFIG, N) \
pzcorebus_array_if_packer #( \
  .BUS_CONFIG (IF_CONFIG  ), \
  .SIZE       (N          ) \
) u_``PREFIX``_packer ( \
  .corebus_if     (IF_NAME                    ), \
  .o_mcmd_valid   (o_``PREFIX``_mcmd_valid    ), \
  .i_scmd_accept  (i_``PREFIX``_scmd_accept   ), \
  .o_mcmd         (o_``PREFIX``_mcmd          ), \
  .o_mdata_valid  (o_``PREFIX``_mdata_valid   ), \
  .i_sdata_accept (i_``PREFIX``_sdata_accept  ), \
  .o_mdata        (o_``PREFIX``_mdata         ), \
  .i_sresp_valid  (i_``PREFIX``_sresp_valid   ), \
  .o_mresp_accept (o_``PREFIX``_mresp_accept  ), \
  .i_sresp        (i_``PREFIX``_sresp         ) \
);

`define pzcorebus_unpack_membus_master_if(PREFIX, IF_NAME, IF_CONFIG, N) \
logic [N-1:0]                                                                 PREFIX``_mcmd_valid; \
logic [N-1:0]                                                                 PREFIX``_scmd_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]         PREFIX``_mcmd; \
logic [N-1:0]                                                                 PREFIX``_mdata_valid; \
logic [N-1:0]                                                                 PREFIX``_sdata_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_write_data_width(IF_CONFIG, 1)-1:0]   PREFIX``_mdata; \
logic [N-1:0]                                                                 PREFIX``_sresp_valid; \
logic [N-1:0]                                                                 PREFIX``_mresp_accept; \
logic [N-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]        PREFIX``_sresp; \
pzcorebus_array_if_unpacker #( \
  .BUS_CONFIG (IF_CONFIG  ), \
  .SIZE       (N          ) \
) u_``PREFIX``_unpacker ( \
  .corebus_if     (IF_NAME                ), \
  .i_mcmd_valid   (PREFIX``_mcmd_valid    ), \
  .o_scmd_accept  (PREFIX``_scmd_accept   ), \
  .i_mcmd         (PREFIX``_mcmd          ), \
  .i_mdata_valid  (PREFIX``_mdata_valid   ), \
  .o_sdata_accept (PREFIX``_sdata_accept  ), \
  .i_mdata        (PREFIX``_mdata         ), \
  .o_sresp_valid  (PREFIX``_sresp_valid   ), \
  .i_mresp_accept (PREFIX``_mresp_accept  ), \
  .o_sresp        (PREFIX``_sresp         ) \
);

`define pzcorebus_connect_membus_master_ports(PREFIX) \
.o_``PREFIX``_mcmd_valid    (PREFIX``_mcmd_valid    ), \
.i_``PREFIX``_scmd_accept   (PREFIX``_scmd_accept   ), \
.o_``PREFIX``_mcmd          (PREFIX``_mcmd          ), \
.o_``PREFIX``_mdata_valid   (PREFIX``_mdata_valid   ), \
.i_``PREFIX``_sdata_accept  (PREFIX``_sdata_accept  ), \
.o_``PREFIX``_mdata         (PREFIX``_mdata         ), \
.i_``PREFIX``_sresp_valid   (PREFIX``_sresp_valid   ), \
.o_``PREFIX``_mresp_accept  (PREFIX``_mresp_accept  ), \
.i_``PREFIX``_sresp         (PREFIX``_sresp         )

//----------------------------------------------------------
//  Memory bus bundled slave
//----------------------------------------------------------
`define pzcorebus_define_membus_bundled_slave_ports(PREFIX, IF_CONFIG, REQUESTS, RESPONSES, N) \
output  var [N-1:0][REQUESTS-1:0]                                                               o_``PREFIX``_scmd_accept, \
input   var [N-1:0][REQUESTS-1:0]                                                               i_``PREFIX``_mcmd_valid, \
input   var [N-1:0][REQUESTS-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]       i_``PREFIX``_mcmd, \
output  var [N-1:0][REQUESTS-1:0]                                                               o_``PREFIX``_sdata_accept, \
input   var [N-1:0][REQUESTS-1:0]                                                               i_``PREFIX``_mdata_valid, \
input   var [N-1:0][REQUESTS-1:0][pzcorebus_pkg::get_packed_write_data_width(IF_CONFIG, 1)-1:0] i_``PREFIX``_mdata, \
input   var [N-1:0][RESPONSES-1:0]                                                              i_``PREFIX``_mresp_accept, \
output  var [N-1:0][RESPONSES-1:0]                                                              o_``PREFIX``_sresp_valid, \
output  var [N-1:0][RESPONSES-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]     o_``PREFIX``_sresp

`define pzcorebus_unpack_membus_bundled_slave_if(PREFIX, IF_NAME, IF_CONFIG, REQUESTS, RESPONSES, N) \
pzcorebus_bundled_array_if_unpacker #( \
  .BUS_CONFIG         (IF_CONFIG  ), \
  .REQUEST_CHANNELS   (REQUESTS   ), \
  .RESPONSE_CHANNELS  (RESPONSES  ), \
  .SIZE               (N                  ) \
) u_``PREFIX``_unpacker ( \
  .corebus_if     (IF_NAME                ), \
  .o_scmd_accept  (o_``PREFIX``_scmd_accept   ), \
  .i_mcmd_valid   (i_``PREFIX``_mcmd_valid    ), \
  .i_mcmd         (i_``PREFIX``_mcmd          ), \
  .o_sdata_accept (o_``PREFIX``_sdata_accept  ), \
  .i_mdata_valid  (i_``PREFIX``_mdata_valid   ), \
  .i_mdata        (i_``PREFIX``_mdata         ), \
  .i_mresp_accept (i_``PREFIX``_mresp_accept  ), \
  .o_sresp_valid  (o_``PREFIX``_sresp_valid   ), \
  .o_sresp        (o_``PREFIX``_sresp         ) \
);

`define pzcorebus_pack_membus_bundled_slave_if(PREFIX, IF_NAME, IF_CONFIG, REQUESTS, RESPONSES, N) \
logic [N-1:0][REQUESTS-1:0]                                                               PREFIX``_scmd_accept; \
logic [N-1:0][REQUESTS-1:0]                                                               PREFIX``_mcmd_valid; \
logic [N-1:0][REQUESTS-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]       PREFIX``_mcmd; \
logic [N-1:0][REQUESTS-1:0]                                                               PREFIX``_sdata_accept; \
logic [N-1:0][REQUESTS-1:0]                                                               PREFIX``_mdata_valid; \
logic [N-1:0][REQUESTS-1:0][pzcorebus_pkg::get_packed_write_data_width(IF_CONFIG, 1)-1:0] PREFIX``_mdata; \
logic [N-1:0][RESPONSES-1:0]                                                              PREFIX``_mresp_accept; \
logic [N-1:0][RESPONSES-1:0]                                                              PREFIX``_sresp_valid; \
logic [N-1:0][RESPONSES-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]     PREFIX``_sresp; \
pzcorebus_bundled_array_if_packer #( \
  .BUS_CONFIG         (IF_CONFIG  ), \
  .REQUEST_CHANNELS   (REQUESTS   ), \
  .RESPONSE_CHANNELS  (RESPONSES  ), \
  .SIZE               (N                  ) \
) u_``PREFIX``_packer ( \
  .corebus_if     (IF_NAME                ), \
  .i_scmd_accept  (PREFIX``_scmd_accept   ), \
  .o_mcmd_valid   (PREFIX``_mcmd_valid    ), \
  .o_mcmd         (PREFIX``_mcmd          ), \
  .i_sdata_accept (PREFIX``_sdata_accept  ), \
  .o_mdata_valid  (PREFIX``_mdata_valid   ), \
  .o_mdata        (PREFIX``_mdata         ), \
  .o_mresp_accept (PREFIX``_mresp_accept  ), \
  .i_sresp_valid  (PREFIX``_sresp_valid   ), \
  .i_sresp        (PREFIX``_sresp         ) \
);

`define pzcorebus_connect_membus_bundled_slave_ports(PREFIX) \
`pzcorebus_connect_membus_slave_ports(PREFIX)

//----------------------------------------------------------
//  Memory bus bundled master
//----------------------------------------------------------
`define pzcorebus_define_membus_bundled_master_ports(PREFIX, IF_CONFIG, REQUESTS, RESPONSES, N) \
input   var [N-1:0][REQUESTS-1:0]                                                               i_``PREFIX``_scmd_accept, \
output  var [N-1:0][REQUESTS-1:0]                                                               o_``PREFIX``_mcmd_valid, \
output  var [N-1:0][REQUESTS-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]       o_``PREFIX``_mcmd, \
input   var [N-1:0][REQUESTS-1:0]                                                               i_``PREFIX``_sdata_accept, \
output  var [N-1:0][REQUESTS-1:0]                                                               o_``PREFIX``_mdata_valid, \
output  var [N-1:0][REQUESTS-1:0][pzcorebus_pkg::get_packed_write_data_width(IF_CONFIG, 1)-1:0] o_``PREFIX``_mdata, \
output  var [N-1:0][RESPONSES-1:0]                                                              o_``PREFIX``_mresp_accept, \
input   var [N-1:0][RESPONSES-1:0]                                                              i_``PREFIX``_sresp_valid, \
input   var [N-1:0][RESPONSES-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]     i_``PREFIX``_sresp

`define pzcorebus_pack_membus_bundled_master_if(PREFIX, IF_NAME, IF_CONFIG, REQUESTS, RESPONSES, N) \
pzcorebus_bundled_array_if_packer #( \
  .BUS_CONFIG         (IF_CONFIG  ), \
  .REQUEST_CHANNELS   (REQUESTS   ), \
  .RESPONSE_CHANNELS  (RESPONSES  ), \
  .SIZE               (N                  ) \
) u_``PREFIX``_packer ( \
  .corebus_if     (IF_NAME                ), \
  .i_scmd_accept  (i_``PREFIX``_scmd_accept   ), \
  .o_mcmd_valid   (o_``PREFIX``_mcmd_valid    ), \
  .o_mcmd         (o_``PREFIX``_mcmd          ), \
  .i_sdata_accept (i_``PREFIX``_sdata_accept  ), \
  .o_mdata_valid  (o_``PREFIX``_mdata_valid   ), \
  .o_mdata        (o_``PREFIX``_mdata         ), \
  .o_mresp_accept (o_``PREFIX``_mresp_accept  ), \
  .i_sresp_valid  (i_``PREFIX``_sresp_valid   ), \
  .i_sresp        (i_``PREFIX``_sresp         ) \
);

`define pzcorebus_unpack_membus_bundled_master_if(PREFIX, IF_NAME, IF_CONFIG, REQUESTS, RESPONSES, N) \
logic [N-1:0][REQUESTS-1:0]                                                               PREFIX``_mcmd_valid; \
logic [N-1:0][REQUESTS-1:0]                                                               PREFIX``_scmd_accept; \
logic [N-1:0][REQUESTS-1:0][pzcorebus_pkg::get_packed_command_width(IF_CONFIG)-1:0]       PREFIX``_mcmd; \
logic [N-1:0][REQUESTS-1:0]                                                               PREFIX``_mdata_valid; \
logic [N-1:0][REQUESTS-1:0]                                                               PREFIX``_sdata_accept; \
logic [N-1:0][REQUESTS-1:0][pzcorebus_pkg::get_packed_write_data_width(IF_CONFIG, 1)-1:0] PREFIX``_mdata; \
logic [N-1:0][RESPONSES-1:0]                                                              PREFIX``_sresp_valid; \
logic [N-1:0][RESPONSES-1:0]                                                              PREFIX``_mresp_accept; \
logic [N-1:0][RESPONSES-1:0][pzcorebus_pkg::get_packed_response_width(IF_CONFIG)-1:0]     PREFIX``_sresp; \
pzcorebus_bundled_array_if_unpacker #( \
  .BUS_CONFIG         (IF_CONFIG  ), \
  .REQUEST_CHANNELS   (REQUESTS   ), \
  .RESPONSE_CHANNELS  (RESPONSES  ), \
  .SIZE               (N                  ) \
) u_``PREFIX``_unpacker ( \
  .corebus_if     (IF_NAME                ), \
  .o_scmd_accept  (PREFIX``_scmd_accept   ), \
  .i_mcmd_valid   (PREFIX``_mcmd_valid    ), \
  .i_mcmd         (PREFIX``_mcmd          ), \
  .o_sdata_accept (PREFIX``_sdata_accept  ), \
  .i_mdata_valid  (PREFIX``_mdata_valid   ), \
  .i_mdata        (PREFIX``_mdata         ), \
  .i_mresp_accept (PREFIX``_mresp_accept  ), \
  .o_sresp_valid  (PREFIX``_sresp_valid   ), \
  .o_sresp        (PREFIX``_sresp         ) \
);

`define pzcorebus_connect_membus_bundled_master_ports(PREFIX) \
`pzcorebus_connect_membus_master_ports(PREFIX)

`endif
