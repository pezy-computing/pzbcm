##========================================
##
## Copyright (c) 2022 PEZY Computing, K.K.
##
##========================================
file_list 'pzbcm.list.rb', from: :current
file_list 'pzvbus_common/pzvbus_common.list.rb'

find_files 'pzvbus_*/*.list.rb', from: :current do |list|
  file_list list
end
