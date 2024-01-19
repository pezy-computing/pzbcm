//========================================
//
// Copyright (c) 2024 PEZY Computing, K.K.
//                    All Rights Reserved.
//
//========================================
package pzcorebus_dummy_pkg;
  import  pzcorebus_pkg::*;

  function automatic bit [31:0] get_error_data(pzcorebus_config bus_config);
    if (is_csr_profile(bus_config)) begin
      return 32'hdead_dead;
    end
    else begin
      return 32'hdead_beaf;
    end
  endfunction
endpackage
