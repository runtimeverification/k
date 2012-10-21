require "bool.k"
module K-EQUAL-HOOKS
  imports #K-EQUAL-INTERFACE
  imports BOOL-HOOKS
  

  syntax Bool ::= left:
  				  K "==K" K           [function, hook(#K-EQUAL:_==K_), latex({#1}\mathrel{=_K}{#2})]
				| K "=/=K" K          [function, latex({#1}\mathrel{\neq_K}{#2})]
  rule K1:K =/=K K2:K => notBool(K1 ==K K2)


  syntax K ::= "#if" Bool "#then" K "#else" K "#fi"   [function]
  rule #if true #then K:K #else _ #fi => K
  rule #if false #then _ #else K:K #fi => K

  // inclusion between sets
  syntax Bool ::= Set "<=Set" Set    [function]
  rule SetItem(K:K) Set1:Set <=Set SetItem(K) Set2:Set => Set1 <=Set Set2
  rule .Set <=Set _:Set => true
  rule SetItem(K:K) Set1:Set <=Set Set2:Set => false
                            when notBool (K in Set2:Set)
  // equality over sets
  syntax Bool ::= Set "==Set" Set    [function]
  rule Set1:Set ==Set Set2:Set => (Set1 <=Set Set2) andBool (Set2 <=Set Set1) 

  // disequality over sets
  syntax Bool ::= Set "=/=Set" Set   [function]
  rule Set1:Set =/=Set Set2:Set => notBool(Set1 ==Set Set2)

  // inclusion between maps
  syntax Bool ::= Map "<=Map" Map    [function]

  rule (MapItem1:MapItem Map1:Map) <=Map (MapItem1 Map2:Map)
        =>
       (Map1 <=Map Map2)


  rule .Map <=Map _:Map => true [function, anywhere]

  rule ((K1:K |-> K2:K) Map1:Map) <=Map Map2 => false
       when notBool $hasMapping(Map2, K1)
       orElseBool (K2 =/=K Map2:Map(K1))


  // equality over maps
  syntax Bool ::= Map "==Map" Map    [function]

  rule Map1:Map ==Map Map2:Map
       =>
      (Map1 <=Map Map2) andBool (Map2 <=Map Map1)


  // disequality over maps
  syntax Bool ::= Map "=/=Map" Map   [function]
  rule Map1:Map =/=Map Map2:Map => notBool(Map1 ==Map Map2)


  // equality over List{K}
  syntax Bool ::= List{K} "==List{K}" List{K}    [function]
  rule LK1:List{K} ==List{K} LK2:List{K} => 'dummy(LK1) ==K 'dummy(LK2)

  // disequality over List{K}
  syntax Bool ::= List{K} "=/=List{K}" List{K}   [function]
  rule LK1:List{K} =/=List{K} LK2:List{K}  => notBool(LK1 ==List{K} LK2)

  // equality over KLabel
  syntax Bool ::= KLabel "==KLabel" KLabel   [function]
  rule '_==KLabel_(K1:K,,K2:K) => K1 ==K K2 [function, anywhere]

  // disequality over KLabel
  syntax Bool ::= KLabel "=/=KLabel" KLabel  [function]
  rule Lbl1:KLabel =/=KLabel Lbl2:KLabel => notBool(Lbl1 ==KLabel Lbl2)

  // equality over lists
  syntax Bool ::= List "==List" List [function]
  rule ListItem(K1:K) L1:List ==List ListItem(K2:K) L2:List
       =>
       K1 ==K K2 andBool L1 ==List L2
  rule .List ==List ListItem(_:K) _:List => false
  rule ListItem(_:K) _:List ==List .List => false
  rule .List ==List .List => true

  // disequality over lists
  syntax Bool ::= List "=/=List" List [function]
  rule L1:List =/=List L2:List => notBool(L1 ==List L2)

endmodule
