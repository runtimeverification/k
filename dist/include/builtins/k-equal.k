require "bool.k"
module K-EQUAL-HOOKS
  imports BOOL-HOOKS

  syntax Bool ::= K "==K" K           [function, hook(#K-EQUAL:_==K_)]
  syntax Bool ::= K "=/=K" K          [function]
  rule K1:K =/=K K2:K => notBool(K1 ==K K2) [function, anywhere]


  syntax K ::= "#if" Bool "#then" K "#else" K "#fi"   [function]
  rule #if true #then K:K #else _ #fi => K [function, anywhere]
  rule #if false #then _ #else K:K #fi => K [function, anywhere]

  syntax Bool ::= Set "<=Set" Set    [function]
  rule SetItem(K:K) Set1:Set <=Set SetItem(K) Set2:Set => Set1 <=Set Set2 [function, anywhere]
  rule .Set <=Set _:Set => true [function, anywhere]
  rule SetItem(K:K) Set1:Set <=Set Set2:Set => false
                            when notBool (K in Set2) [function, anywhere]

  syntax Bool ::= Set "==Set" Set    [function]
  rule Set1:Set ==Set Set2:Set => (Set1 <=Set Set2) andBool (Set2 <=Set Set1) [function, anywhere]

  syntax Bool ::= Set "=/=Set" Set   [function]
  rule Set1:Set =/=Set Set2:Set => notBool(Set1 ==Set Set2) [function, anywhere]

  syntax Bool ::= List{K} "==List{K}" List{K}    [function]
  rule LK1:List{K} ==List{K} LK2:List{K} => 'dummy(LK1) ==K 'dummy(LK2) [function, anywhere]

  syntax Bool ::= List{K} "=/=List{K}" List{K}   [function]
  rule LK1:List{K} =/=List{K} LK2:List{K}  => notBool(LK1 ==List{K} LK2) [function, anywhere]

  syntax Bool ::= KLabel "==KLabel" KLabel   [function]
  rule '_==KLabel_(K1:K,,K2:K) => K1 ==K K2 [function, anywhere]

endmodule
