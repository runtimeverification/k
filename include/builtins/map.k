require "builtins/bag.k"
require "builtins/set.k"


module MAP
  imports BAG
  imports SET

  /*@\section{Description} The Map represents a generalized associative array;
   arbitrary keys can be paired with arbitrary values; the values can later
   be referenced using the key.
  (TODO: What are all these "MyMap"s doing? how are they different from Maps?) 
  */

  /*@ Construct a new Map consisting of key-value pairs of multiple Maps (deep copy) (TODO: double-check this):*/
  syntax MyMap ::= MyMap "," MyMap    [left,function, hook(Map:__), klabel('_Map_)]
  /*@  Construct an empty Map: */
  syntax MyMap ::= ".MyMap"       [function, hook(Map:.Map)]
  /*@ This construct is used to refer to key-value pairs within a map, with the 
   key on the left and the value on the right: */
  syntax MyMap ::= K "|->" K      [function, hook(Map:_|->_)]
                 // breaks klabel uniqueness
                 //| "."            [function, hook(Map:.Map)]
  syntax priorities '_|->_ > '_Map_ '.MyMap

  /*@ Construct a map from two lists, the first list containing keys and the
   second list containing values (TODO: Difference between Lists and KLists?
   What happens if the lists are of different sizes?): */
  syntax MyMap ::= MyMapOf(KList, KList)    [function]
//  rule MyMapOf(K1:K,,KL1:KList, K2:K,,KL2:KList) => K1 |-> K2 MyMapOf(KL1, KL2)
//  rule MyMapOf(.KList, .KList) => .MyMap

  /*@ Retreive the value associated with the given key: */
  // AndreiS: using () instead of [] causes ambiguities with __
  // () cannot be used for disambiguation
  syntax K ::= MyMap "[" K "]"    [function, hook(Map:lookup), klabel(Map:lookup)]
//  rule (K1:K |-> K2:K _:MyMap)[K1] => K2

  /*@ Update a Map in form of KLists of keys and values:
 (TODO: There are no KLists here. What it this function actually doing?) */
  syntax MyMap ::= MyMap "[" K "<-" K "]"    [function, hook(Map:update), prefer]
//  rule (K1:K |-> _ M:MyMap)[K1 <- K2:K] => K1 |-> K2 M
//  rule M:MyMap[K1:K <- K2:K] => K1 |-> K2 M
//  when notBool(K1 in keys(M))
  //syntax MyMap ::= MyMap "[" KList "<-" KList "]"    [function, hook(Map:update)]
  //rule
  //  M:MyMap[K2:K,,K4:K,,KL2:KList <- K1:K,,K3:K,,KL1:KList]
  //=>
  //  M[K2 <- K1][K4 <- K3][KL2 <- KL1]
  //rule M:MyMap[.KList <- .KList] => M
  //rule (K1:K |-> _ M:MyMap)[K1 <- K2:K] => K1 |-> K2 M
  //rule M:MyMap[K1:K <- K2:K] => K1 |-> K2 M
  //when notBool(K1 in keys(M))

  /*@ Update the first map by adding all key-value pairs in the second map. 
   If a key in the first map exists also in the second map, its associated value
   will be overwritten by the value from the second map.*/
  // TODO: rename operator
  syntax MyMap ::= update(MyMap, MyMap)   [function]
//  rule update(M1:MyMap, K1:K |-> K2:K M2:MyMap) => update(M1[K1 <- K2], M2)
//  rule update(M:MyMap, .MyMap) => M

  /*@ map domain restriction (TODO: what does this mean? Remove key from map? This will aslo remove the resulting value, right?) */
  syntax MyMap ::= MyMap "[" K "<-" "undef" "]"    [function, hook(Map:remove)] 
//  rule
//    M:MyMap[K1:K,,K2:K,,KL:KList <- undef]
//  =>
//    M[K1 <- undef][K2 <- undef][KL <- undef]
//  rule (K:K |-> _ M:MyMap)[K <- undef] => M
//  rule M:MyMap[.KList <- undef] => M

  /*@ Construct a Set consisting of all keys in the Map (TODO: What is the difference between Sets and MySets?):*/
	syntax MySet ::= keys(MyMap)    [function, hook(Map:keys)]
//  rule keys(K:K |-> _ M:MyMap) => MySetItem(K) keys(M)
//  rule keys(.MyMap) => .MySet

  /*@ Construct a Bag consisting of all values in the Map: */
	syntax MyBag ::= values(MyMap)    [function]
//  rule values(_ |-> K:K M:MyMap) => MyBagItem(K) values(M)
//  rule values(.MyMap) => .MyBag

  /*@ Get Map size (TODO: number of key/value pairs? Total combined number of keys and values?):*/
  syntax Int ::= size(MyMap)   [function]
//  rule size(_ |-> _ M:MyMap) => 1 +Int size(M)
//  rule size(.MyMap) => 0
endmodule

