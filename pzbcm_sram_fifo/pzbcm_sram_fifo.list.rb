##========================================
##
## Copyright (c) 2023 PEZY Computing, K.K.
##                    All Rights Reserved.
##
##========================================
['pzbcm_fifo', 'pzbcm_sram'].each do |bcm|
  file_list "#{bcm}/#{bcm}.list.rb", from: :local_root
end

source_file 'pzbcm_sram_fifo.sv'
