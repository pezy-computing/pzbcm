##========================================
##
## Copyright (c) 2022 PEZY Computing, K.K.
##                    All Rights Reserved.
##
##========================================
include_directory '.'

[
  'pzcorebus_macros.svh',
  'pzcorebus_pkg.sv',
  'pzcorebus_if_pkg.sv',
  'pzcorebus_if_internal_macros.svh',
  'pzcorebus_if.sv',
  'pzcorebus_request_if.sv',
  'pzcorebus_response_if.sv',
  'pzcorebus_bundled_if.sv',
  'pzcorebus_connector.sv',
  'pzcorebus_transposer.sv',
  'pzcorebus_id_assigner.sv',
  'pzcorebus_broadcast_forcer.sv',
  'pzcorebus_base_address_remover.sv',
  'pzcorebus_if_packer.sv',
  'pzcorebus_if_unpacker.sv',
  'pzcorebus_array_if_packer.sv',
  'pzcorebus_array_if_unpacker.sv',
  'pzcorebus_if_bundler.sv',
  'pzcorebus_if_unbundler.sv',
  'pzcorebus_bundled_array_if_packer.sv',
  'pzcorebus_bundled_array_if_unpacker.sv',
].each { |file| source_file file }
