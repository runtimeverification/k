require "builtins/bag.k"
require "builtins/set.k"


module MAP
  imports BAG
  imports SET

  syntax Map ::= Map Map        [left,function, hook(Map:__), klabel('_Map_)]
               | ".Map"         [function, hook(Map:.Map)]
               | K "|->" K      [function, hook(Map:_|->_)]
               // breaks klabel uniqueness
               //| "."          [function, hook(Map:.Map)]
  syntax priorities '_|->_ > '_Map_ '.Map

  /* map of keys and values */
  syntax Map ::= MapOf(KList, KList)    [function]
//  rule MapOf(K1:K,,KL1:KList, K2:K,,KL2:KList) => K1 |-> K2 MapOf(KL1, KL2)
//  rule MapOf(.KList, .KList) => .Map

  /* map key lookup */
  // AndreiS: using () instead of [] causes ambiguities with __
  // () cannot be used for disambiguation
  syntax K ::= Map "[" K "]"    [function, hook(Map:lookup), klabel(Map:lookup)]
//  rule (K1:K |-> K2:K _:Map)[K1] => K2

  /* map values update (update in form of KLists of keys and values) */
  syntax Map ::= Map "[" K "<-" K "]"    [function, hook(Map:update), prefer]
//  rule (K1:K |-> _ M:Map)[K1 <- K2:K] => K1 |-> K2 M
//  rule M:Map[K1:K <- K2:K] => K1 |-> K2 M
//  when notBool(K1 in keys(M))
  //syntax Map ::= Map "[" KList "<-" KList "]"    [function, hook(Map:update)]
  //rule
  //  M:Map[K2:K,,K4:K,,KL2:KList <- K1:K,,K3:K,,KL1:KList]
  //=>
  //  M[K2 <- K1][K4 <- K3][KL2 <- KL1]
  //rule M:Map[.KList <- .KList] => M
  //rule (K1:K |-> _ M:Map)[K1 <- K2:K] => K1 |-> K2 M
  //rule M:Map[K1:K <- K2:K] => K1 |-> K2 M
  //when notBool(K1 in keys(M))

  /* map values update (update in form of a second map) */
  // TODO: rename operator
  syntax Map ::= update(Map, Map)   [function]
//  rule update(M1:Map, K1:K |-> K2:K M2:Map) => update(M1[K1 <- K2], M2)
//  rule update(M:Map, .Map) => M

  /* map domain restriction */
  syntax Map ::= Map "[" K "<-" "undef" "]"    [function, hook(Map:remove)]
//  rule
//    M:Map[K1:K,,K2:K,,KL:KList <- undef]
//  =>
//    M[K1 <- undef][K2 <- undef][KL <- undef]
//  rule (K:K |-> _ M:Map)[K <- undef] => M
//  rule M:Map[.KList <- undef] => M

  /* set of map keys */
	syntax Set ::= keys(Map)    [function, hook(Map:keys)]
//  rule keys(K:K |-> _ M:Map) => SetItem(K) keys(M)
//  rule keys(.Map) => .Set

  /* bag of map values */
	syntax List ::= values(Map)    [function]
//  rule values(_ |-> K:K M:Map) => BagItem(K) values(M)
//  rule values(.Map) => .Bag

  /* map size */
  syntax Int ::= size(Map)   [function]
//  rule size(_ |-> _ M:Map) => 1 +Int size(M)
//  rule size(.Map) => 0
endmodule

