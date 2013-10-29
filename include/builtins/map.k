require "builtins/bag.k"
require "builtins/set.k"


module MAP
  imports BAG
  imports SET

  syntax MyMap ::= MyMap MyMap    [left,function, hook(Map:__), klabel('_Map_)]
                 | ".MyMap"       [function, hook(Map:.Map)]
                 | K "|->" K      [function, hook(Map:_|->_)]
                 // breaks klabel uniqueness
                 //| "."            [function, hook(Map:.Map)]
  syntax priorities '_|->_ > '_Map_ '.MyMap

  /* map of keys and values */
  syntax MyMap ::= MyMapOf(KList, KList)    [function]
  rule MyMapOf(K1:K,,KL1:KList, K2:K,,KL2:KList) => K1 |-> K2 MyMapOf(KL1, KL2)
  rule MyMapOf(.KList, .KList) => .MyMap

  /* map key lookup */
  // AndreiS: using () instead of [] causes ambiguities with __
  // () cannot be used for disambiguation
  syntax K ::= MyMap "[" K "]"    [function, hook(Map:lookup), klabel(Map:lookup)]
  rule (K1:K |-> K2:K _:MyMap)[K1] => K2

  /* map values update (update in form of KLists of keys and values) */
  syntax MyMap ::= MyMap "[" K "<-" K "]"    [function, hook(Map:update), prefer]
  rule (K1:K |-> _ M:MyMap)[K1 <- K2:K] => K1 |-> K2 M
  rule M:MyMap[K1:K <- K2:K] => K1 |-> K2 M
  when notBool(K1 in keys(M))
  //syntax MyMap ::= MyMap "[" KList "<-" KList "]"    [function, hook(Map:update)]
  //rule
  //  M:MyMap[K2:K,,K4:K,,KL2:KList <- K1:K,,K3:K,,KL1:KList]
  //=>
  //  M[K2 <- K1][K4 <- K3][KL2 <- KL1]
  //rule M:MyMap[.KList <- .KList] => M
  //rule (K1:K |-> _ M:MyMap)[K1 <- K2:K] => K1 |-> K2 M
  //rule M:MyMap[K1:K <- K2:K] => K1 |-> K2 M
  //when notBool(K1 in keys(M))

  /* map values update (update in form of a second map) */
  // TODO: rename operator
  syntax MyMap ::= update(MyMap, MyMap)   [function]
  rule update(M1:MyMap, K1:K |-> K2:K M2:MyMap) => update(M1[K1 <- K2], M2)
  rule update(M:MyMap, .MyMap) => M

  /* map domain restriction */
  syntax MyMap ::= MyMap "[" KList "<-" "undef" "]"    [function] 
  rule
    M:MyMap[K1:K,,K2:K,,KL:KList <- undef]
  =>
    M[K1 <- undef][K2 <- undef][KL <- undef]
  rule (K:K |-> _ M:MyMap)[K <- undef] => M
  rule M:MyMap[.KList <- undef] => M

  /* set of map keys */
	syntax MySet ::= keys(MyMap)    [function, hook(Map:keys)]
  rule keys(K:K |-> _ M:MyMap) => MySetItem(K) keys(M)
  rule keys(.MyMap) => .MySet

  /* bag of map values */
	syntax MyBag ::= values(MyMap)    [function]
  rule values(_ |-> K:K M:MyMap) => MyBagItem(K) values(M)
  rule values(.MyMap) => .MyBag

  /* map size */
  syntax Int ::= size(MyMap)   [function]
  rule size(_ |-> _ M:MyMap) => 1 +Int size(M)
  rule size(.MyMap) => 0
endmodule

