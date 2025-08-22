##========================================
##
## Copyright (c) 2022 PEZY Computing, K.K.
##
##========================================
file_list   'pzbcm_min_max_finder/pzbcm_min_max_finder.list.rb'
file_list   'pzbcm_onehot/pzbcm_onehot.list.rb'
source_file 'pzbcm_arbiter_pkg.sv'
source_file 'pzbcm_matrix_arbiter.sv'
source_file 'pzbcm_round_robin_arbiter.sv'
source_file 'pzbcm_arbiter.sv'

if macro_defined? :PZBCM_ARBITER_ENABLE_SVA
  source_file 'tb_pzbcm_matrix_arbiter_sva.sv'
end
