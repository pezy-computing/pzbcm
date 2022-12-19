file_list 'pzbcm.list.rb', from: :current

%w(
  pzhsbus_common
  pzhsbus_async_fifo
  pzhsbus_fifo
  pzhsbus_selector
  pzhsbus_slicer
).each do |hsbus_module|
  file_list "#{hsbus_module}/#{hsbus_module}.list.rb", from: :current
end
