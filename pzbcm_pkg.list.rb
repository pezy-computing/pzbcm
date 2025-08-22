##========================================
##
## Copyright (c) 2023 PEZY Computing, K.K.
##
##========================================
find_files 'pzbcm_*/*_pkg.sv', from: :current do |pkg|
  source_file pkg
end
