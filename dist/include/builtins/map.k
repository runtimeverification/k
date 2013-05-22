require "builtins/bag.k"
require "builtins/set.k"


module MAP
  imports BAG
  imports SET

  syntax MyMap ::= MyMap MyMap    [function, hook(Map:__), klabel('_Map_)]
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
  // AndreiS: using () instead of [] causes too ambiguities with __ and ()
  // cannot be used for disambiguation
  syntax K ::= MyMap "[" K "]"    [function]
  rule (K1:K |-> K2:K _:MyMap)[K1] => K2

  /* map values update (update in form of KLists of keys and values) */
  syntax MyMap ::= MyMap "[" KList "/" KList "]"    [function]
  rule
    M:MyMap[K2:K,,K4:K,,KL2:KList / K1:K,,K3:K,,KL1:KList]
  =>
    M[K2 / K1][K4 / K3][KL2 / KL1]
  rule M:MyMap[.KList / .KList] => M
  rule (K1:K |-> _ M:MyMap)[K2:K / K1] => K1 |-> K2 M
  rule M:MyMap[K2:K / K1:K] => K1 |-> K2 M
  when notBool(K1 in keys(M))

  /* map values update (update in form of a second map) */
  syntax MyMap ::= MyMap "[" MyMap "]"    [function]
  rule M1:MyMap[K1:K |-> K2:K M2:MyMap] => M1[K2 / K1][M2]
  rule M:MyMap[.MyMap] => M

  /* map domain restriction */
  syntax MyMap ::= MyMap "[" "undef" "/" KList "]"    [function] 
  rule
    M:MyMap[undef / K1:K,,K2:K,,KL:KList]
  =>
    M[undef / K1][undef / K2][undef / KL]
  rule (K:K |-> _ M:MyMap)[undef / K] => M
  rule M:MyMap[undef / .KList] => M

  /* set of map keys */
	syntax MySet ::= keys(MyMap)    [function]
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

