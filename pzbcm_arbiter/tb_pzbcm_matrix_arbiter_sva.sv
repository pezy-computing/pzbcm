module tb_pzbcm_matrix_arbiter_sva #(
  parameter int REQUESTS  = 2
)(
  input var                               i_clk,
  input var                               i_rst_n,
  input var [REQUESTS-1:0]                i_request,
  input var [REQUESTS-1:0]                i_grant,
  input var [REQUESTS-1:0][REQUESTS-1:0]  i_priority_matrix
);
`ifdef  _PZ_UVM_
  import  uvm_pkg::*;
  `include  "uvm_macros.svh"

  function automatic void print_error(string checker_name);
    `uvm_fatal("SVA", $sformatf("checker: %s is failed", checker_name))
  endfunction
`else
  function automatic void print_error(string checker_name);
    $fatal($sformatf("checker: %s is failed", checker_name));
  endfunction
`endif
  bit update_grant;

  always_comb begin
    update_grant  = i_request != '0;
  end

  int row_values[REQUESTS];
  int columun_values[REQUESTS];

  always_comb begin
    for (int i = 0;i < REQUESTS;++i) begin
      bit [REQUESTS-1:0]  row;
      bit [REQUESTS-1:0]  columun;

      row = i_priority_matrix[i];
      for (int j = 0;j < REQUESTS;++j) begin
        columun[j]  = i_priority_matrix[j][i];
      end

      row_values[i]     = $countones(row);
      columun_values[i] = $countones(columun);
    end
  end

  function automatic bit is_unique(int array[REQUESTS]);
    int q[$];
    q = array.unique;
    return q.size() == REQUESTS;
  endfunction

  property p_request_should_not_be_unknown;
    @(posedge i_clk) disable iff (!i_rst_n)
    !$isunknown(i_request);
  endproperty

  property p_row_values_should_be_unique;
    @(posedge i_clk) disable iff (!i_rst_n)
    is_unique(row_values);
  endproperty

  property p_column_values_should_be_unique;
    @(posedge i_clk) disable iff (!i_rst_n)
    is_unique(columun_values);
  endproperty

  property p_grant_should_be_onehot;
    @(posedge i_clk) disable iff (!i_rst_n)
    (update_grant) |-> $onehot(i_grant);
  endproperty

  property p_grant_should_be_for_active_request;
    @(posedge i_clk) disable iff (!i_rst_n)
    (update_grant) |-> ((i_request & i_grant) != '0);
  endproperty

  asm_request_should_not_be_unknown:
  assume property(p_request_should_not_be_unknown)
  else print_error("asm_request_should_not_be_unknown");

  ast_row_values_should_be_unique:
  assert property(p_row_values_should_be_unique)
  else print_error("ast_row_values_should_be_unique");

  ast_column_values_should_be_unique:
  assert property(p_column_values_should_be_unique)
  else print_error("ast_column_values_should_be_unique");

  ast_grant_should_be_onehot:
  assert property(p_grant_should_be_onehot)
  else print_error("ast_grant_should_be_onehot");

  ast_grant_should_be_for_active_request:
  assert property(p_grant_should_be_for_active_request)
  else print_error("ast_grant_should_be_for_active_request");
endmodule
