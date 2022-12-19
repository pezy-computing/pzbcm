file_list 'pzbcm.list.rb', from: :current

%w(
  pzvbus_common
  pzvbus_async_fifo
  pzvbus_fifo
  pzvbus_selector
).each do |pzvbus_module|
  file_list "#{pzvbus_module}/#{pzvbus_module}.list.rb", from: :current
end
