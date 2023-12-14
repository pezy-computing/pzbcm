##========================================
##
## Copyright (c) 2023 PEZY Computing, K.K.
##                    All Rights Reserved.
##
##========================================
find_files 'pzbcm_*/*_pkg.sv', from: :current do |pkg|
  source_file pkg
end
