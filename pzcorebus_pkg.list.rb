##========================================
##
## Copyright (c) 2023 PEZY Computing, K.K.
##                    All Rights Reserved.
##
##========================================
source_file 'pzcorebus_common/pzcorebus_pkg.sv'
find_files 'pzcorebus_*/*_pkg.sv', from: :current do |pkg|
  source_file pkg
end
