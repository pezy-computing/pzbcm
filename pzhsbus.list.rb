##========================================
##
## Copyright (c) 2022 PEZY Computing, K.K.
##                    All Rights Reserved.
##
##========================================
file_list 'pzbcm.list.rb', from: :current
file_list 'pzhsbus_common/pzhsbus_common.list.rb', from: :current

find_files 'pzhsbus_*/*.list.rb', from: :current do |list|
  file_list list
end
