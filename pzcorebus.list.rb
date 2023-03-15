##========================================
##
## Copyright (c) 2022 PEZY Computing, K.K.
##                    All Rights Reserved.
##
##========================================
file_list 'pzbcm.list.rb', from: :current

%w(
  pzcorebus_common
  pzcorebus_1_to_m_switch
  pzcorebus_async_fifo
  pzcorebus_axi_bridge
  pzcorebus_command_data_aligner
  pzcorebus_debug
  pzcorebus_downsizer
  pzcorebus_dummy
  pzcorebus_fifo
  pzcorebus_gate
  pzcorebus_m_to_1_switch
  pzcorebus_membus2csrbus_adapter
  pzcorebus_packer
  pzcorebus_rmw_converter
  pzcorebus_selector
  pzcorebus_slicer
  pzcorebus_upsizer
).each do |corebus_module|
  file_list "#{corebus_module}/#{corebus_module}.list.rb", from: :current
end
