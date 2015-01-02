// Copyright (c) 2012-2015 K Team. All Rights Reserved.
require "bool.k"
require "list.k"
require "map.k"
require "set.k"
require "k-prelude.k"


module K-EQUAL-HOOKS
  imports BOOL-HOOKS
  imports LIST
  imports MAP
  imports SET
  imports K-TECHNIQUE


  syntax Bool ::= left:
                    K "==K" K           [function, smtlib(=), hook(#K-EQUAL:_==K_), latex({#1}\mathrel{=_K}{#2}), equalEqualK]
                | K "=/=K" K          [function, smtlib(distinct), hook(#K-EQUAL:_=/=K_), latex({#1}\mathrel{\neq_K}{#2}), notEqualEqualK]

  syntax priorities equalEqualK notEqualEqualK > boolOperation
  rule K1:K =/=K K2:K => notBool(K1 ==K K2)

  // this is really problematic, needs to be discussed
  //syntax KList ::= "#if" Bool "#then" KList "#else" KList "#fi"   [function, hook(KEqual:ite)]
  syntax K     ::= "#if" Bool "#then" K     "#else" K     "#fi"   [function, hook(KEqual:ite)]
  //syntax KItem ::= "#if" Bool "#then" KItem "#else" KItem "#fi"   [function, hook(KEqual:ite)]
  //syntax Int   ::= "#if" Bool "#then" Int   "#else" Int   "#fi"   [function, smtlib(ite)]
  rule #if true #then K:K #else _:K #fi => K
  rule #if false #then _:K #else K:K #fi => K

  // equality over KList
  syntax Bool ::= KList "==KList" KList    [function, hook(KEqual:_==KList_)]

  syntax KItem ::= dummy(KList)
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


  // TODO(dwightguth): fix once bags are K
  syntax Bool ::= left:
                  Bag "==Bag" Bag           [function, hook(#K-EQUAL:_==K_), latex({#1}\mathrel{=_K}{#2}), equalEqualK]
                | Bag "=/=Bag" Bag          [function, hook(#K-EQUAL:_=/=K_), latex({#1}\mathrel{\neq_K}{#2}), notEqualEqualK]
endmodule
