##========================================
##
## Copyright (c) 2023 PEZY Computing, K.K.
##                    All Rights Reserved.
##
##========================================
[
  'pzbcm_delay', 'pzbcm_fifo', 'pzbcm_ram', 'pzbcm_selector'
].each do |bcm|
  file_list "#{bcm}/#{bcm}.list.rb", from: :local_root
end

source_file 'pzbcm_sram_pkg.sv'
source_file 'pzbcm_sram_if.sv'
source_file 'pzbcm_sram_1rw_wrapper_default.sv'
source_file 'pzbcm_sram_1r1w_wrapper_default.sv'
source_file 'pzbcm_sram.sv'
