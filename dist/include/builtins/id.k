module ID-SYNTAX-HOOKS
  imports #ID-INTERFACE
  syntax Id ::= #Id 
endmodule

module ID-HOOKS
  imports ID-SYNTAX-HOOKS
  imports K

  syntax K ::= vars(Set)

  syntax K ::= getVars(K)
  rule getVars(K) => getVars1(K, .Set)

  syntax K ::= getVars1(List{K}, Set)
  rule getVars1((X:Id => .List{K}),,_, _ (.Set => SetItem(X)))
  rule getVars1((L(Ks) => Ks),,_, _)
    when isId(L(Ks)) =/=K true
  rule getVars1(.List{K}, S) => vars(S)
endmodule
