##========================================
##
## Copyright (c) 2022 PEZY Computing, K.K.
##                    All Rights Reserved.
##
##========================================
file_list   'pzbcm_edge_detector/pzbcm_edge_detector.list.rb'
file_list   'pzbcm_synchronizer/pzbcm_synchronizer.list.rb'
source_file 'pzbcm_async_fifo/pzbcm_async_fifo_reset_sync.sv', from: :local_root
source_file 'pzbcm_async_handshake.sv'
