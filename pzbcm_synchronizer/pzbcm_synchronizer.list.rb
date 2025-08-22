##========================================
##
## Copyright (c) 2022 PEZY Computing, K.K.
##
##========================================
unless macro_defined?(:PZBCM_SYNCHRONIZER_CUSTOM_IMPLEMENTATION)
  custom_implementation =
    Pathname
      .new(__dir__)
      .ascend
      .map { |path| path.join('pzbcm_synchronizer_custom_implementation.svh') }
      .find(&:file?)
      &.dirname
  if custom_implementation
    define_macro      :PZBCM_SYNCHRONIZER_CUSTOM_IMPLEMENTATION
    include_directory custom_implementation
  end
end

source_file 'pzbcm_synchronizer.sv'
