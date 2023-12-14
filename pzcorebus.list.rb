##========================================
##
## Copyright (c) 2022 PEZY Computing, K.K.
##                    All Rights Reserved.
##
##========================================
file_list 'pzbcm.list.rb', from: :current
file_list 'pzcorebus_common/pzcorebus_common.list.rb', from: :current

find_files 'pzcorebus_*/*.list.rb', from: :current do |list|
  file_list list
end
