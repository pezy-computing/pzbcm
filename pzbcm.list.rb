%w(
  pzbcm_arbiter
  pzbcm_async_fifo
  pzbcm_async_handshake
  pzbcm_counter
  pzbcm_delay
  pzbcm_edge_detector
  pzbcm_fifo
  pzbcm_gray
  pzbcm_min_max_finder
  pzbcm_multi_bits_detector
  pzbcm_onehot
  pzbcm_priority_encoder
  pzbcm_ram
  pzbcm_selector
  pzbcm_slicer
  pzbcm_synchronizer
).each do |bcm_module|
  file_list "#{bcm_module}/#{bcm_module}.list.rb", from: :current
end
