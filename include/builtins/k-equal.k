// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "bool.k"
require "list.k"
require "map.k"
require "set.k"
require "k-prelude.k"


module K-EQUAL-HOOKS
  imports #K-EQUAL-INTERFACE
  imports BOOL-HOOKS
  imports LIST
  imports MAP
  imports SET


  syntax Bool ::= left:
  				  K "==K" K           [function, hook(#K-EQUAL:_==K_), latex({#1}\mathrel{=_K}{#2}), equalEqualK]
				| K "=/=K" K          [function, hook(#K-EQUAL:_=/=K_), latex({#1}\mathrel{\neq_K}{#2}), notEqualEqualK]

  syntax priorities equalEqualK notEqualEqualK > boolOperation
  rule K1:K =/=K K2:K => notBool(K1 ==K K2)


  syntax K ::= "#if" Bool "#then" K "#else" K "#fi"   [function, hook(KEqual:ite)]
  syntax KItem ::= "#if" Bool "#then" KItem "#else" KItem "#fi"   [function, hook(KEqual:ite)]
  syntax KList ::= "#if" Bool "#then" KList "#else" KList "#fi"   [function, hook(KEqual:ite)]
  syntax Int ::= "#if" Bool "#then" Int "#else" Int "#fi"   [function, smtlib(ite)]
  rule #if true #then K:K #else _:K #fi => K
  rule #if false #then _:K #else K:K #fi => K

  // equality over sets
  syntax Bool ::= Set "==Set" Set    [function]
  rule Set1:Set ==Set Set2:Set => (Set1 <=Set Set2) andBool (Set2 <=Set Set1)

  // disequality over sets
  syntax Bool ::= Set "=/=Set" Set   [function]
  rule Set1:Set =/=Set Set2:Set => notBool(Set1 ==Set Set2)

  // equality over maps
  syntax Bool ::= Map "==Map" Map    [function]

  rule Map1:Map ==Map Map2:Map
       =>
      (Map1 <=Map Map2) andBool (Map2 <=Map Map1)


  // disequality over maps
  syntax Bool ::= Map "=/=Map" Map   [function]
  rule Map1:Map =/=Map Map2:Map => notBool(Map1 ==Map Map2)


  // equality over KList
  syntax Bool ::= KList "==KList" KList    [function, hook(KEqual:_==KList_)]

  syntax K ::= dummy(KList)
  rule LK1:KList ==KList LK2:KList => dummy(LK1) ==K dummy(LK2)

  // disequality over KList
  syntax Bool ::= KList "=/=KList" KList   [function, hook(KEqual:_=/=KList_)]
  rule LK1:KList =/=KList LK2:KList  => notBool(LK1 ==KList LK2)

  // equality over KLabel
  syntax Bool ::= KLabel "==KLabel" KLabel
    [function, hook(KEqual:_==KLabel_), latex({#1}\mathrel{=_{\it KLabel}}{#2})]
  rule '_==KLabel_(K1:K,,K2:K) => K1 ==K K2 [function, anywhere]

  // disequality over KLabel
  syntax Bool ::= KLabel "=/=KLabel" KLabel
    [function, hook(KEqual:_=/=KLabel_), latex({#1}\mathrel{\neq_{\it KLabel}}{#2})]
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

  syntax Bool ::= K "=K" K                  [function]
                | List "=List" List         [function]
                | Set "=Set" Set            [function]
                | Bag "=Bag" Bag            [function]
                | Map "=Map" Map            [function]
                | KList "=KList" KList      [function]
                | KLabel "=KLabel" KLabel   [function]

  rule K:K =K K => true

  rule ((K1:K,,KL1:KList) =KList (K2:K,,KL2:KList)) => ((K1 =K K2) andBool (KL1 =KList KL2))
  rule .KList =KList .KList => true
  rule (_:K,,_:KList) =KList .KList => false
  rule .KList =KList (_:K,,_:KList) => false
endmodule
