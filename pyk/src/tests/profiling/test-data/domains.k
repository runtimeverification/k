require "kast.md"


module DOMAINS-SYNTAX
  imports SORT-K
  imports ID-SYNTAX
  imports UNSIGNED-INT-SYNTAX
  imports BOOL-SYNTAX
  imports STRING-SYNTAX
endmodule


module DOMAINS
  imports DOMAINS-SYNTAX
  imports INT
  imports BOOL
  imports STRING
  imports BASIC-K
  imports LIST
  imports K-IO
  imports MAP
  imports SET
  imports ID
  imports K-EQUAL
endmodule


module ARRAY-SYNTAX
  imports private LIST

  syntax Array [hook(ARRAY.Array), unit(arrayCtor), element(_[_<-_])]

  syntax KItem ::= Array "[" Int "]" [function, hook(ARRAY.lookup)]

  syntax Array ::= Array "[" key: Int "<-" value: KItem "]" [function, hook(ARRAY.update), klabel(_[_<-_]), symbol]
  syntax Array ::= Array "[" Int "<-" "undef" "]" [function, hook(ARRAY.remove)]
  syntax Array ::= updateArray(Array, index: Int, List) [function, hook(ARRAY.updateAll)]
  syntax Array ::= fillArray(Array, index: Int, length: Int, value: KItem) [function, hook(ARRAY.fill)]

  syntax Bool ::= Int "in_keys" "(" Array ")" [function, total, hook(ARRAY.in_keys)]
endmodule


module ARRAY-IN-K [private]
  imports public ARRAY-SYNTAX
  imports private LIST
  imports private K-EQUAL
  imports private INT
  imports private BOOL

  syntax Array ::= makeArray(length: Int, value: KItem) [function, hook(ARRAY.make), public]
  syntax Array ::= arr(List, Int, KItem)

  rule makeArray(I::Int, D::KItem) => arr(.List, I, D)

  rule arr(L::List, _, _       ) [ IDX::Int ] => L[IDX] requires 0 <=Int IDX andBool IDX  <Int size(L)
  rule arr(_      , _, D::KItem) [ _        ] => D      [owise]

  syntax List ::= ensureOffsetList(List, Int, KItem) [function]
  rule ensureOffsetList(L::List, IDX::Int, D::KItem) => L makeList(IDX +Int 1 -Int size(L), D) requires         IDX >=Int size(L)
  rule ensureOffsetList(L::List, IDX::Int, _::KItem) => L                                      requires notBool IDX >=Int size(L)

  rule arr(L::List, I::Int, D::KItem) [ IDX::Int <- VAL::KItem ] => arr(ensureOffsetList(L, IDX, D) [ IDX <- VAL ], I, D)

  rule arr(L::List, I::Int, D::KItem) [ IDX::Int <- undef ] => arr(L, I, D) [ IDX <- D ]

  rule updateArray(arr(L::List, I::Int, D::KItem), IDX::Int, L2::List) => arr(updateList(ensureOffsetList(L, IDX +Int size(L2) -Int 1, D), IDX, L2), I, D)

  rule fillArray(arr(L::List, I::Int, D::KItem), IDX::Int, LEN::Int, VAL::KItem) => arr(fillList(ensureOffsetList(L, IDX +Int LEN -Int 1, D), IDX, LEN, VAL), I, D)

  rule IDX::Int in_keys(arr(_, I::Int, _)) => IDX >=Int 0 andBool IDX <Int I
endmodule


module ARRAY-SYMBOLIC [symbolic]
  imports ARRAY-IN-K
endmodule


module ARRAY-KORE [kore]
  imports ARRAY-IN-K
endmodule


module ARRAY
  imports ARRAY-SYMBOLIC
  imports ARRAY-KORE
endmodule


module MAP
  imports private BOOL-SYNTAX
  imports private INT-SYNTAX
  imports private LIST
  imports private SET

  syntax Map [hook(MAP.Map)]

  syntax Map ::= Map Map                        [left, function, hook(MAP.concat), klabel(_Map_), symbol, assoc, comm, unit(.Map), element(_|->_), index(0), format(%1%n%2)]
  syntax Map ::= ".Map"                         [function, total, hook(MAP.unit), klabel(.Map), symbol, latex(\dotCt{Map})]
  syntax Map ::= KItem "|->" KItem                      [function, total, hook(MAP.element), klabel(_|->_), symbol, latex({#1}\mapsto{#2}), injective]

  syntax priorities _|->_ > _Map_ .Map
  syntax non-assoc _|->_

  syntax KItem ::= Map "[" KItem "]"                    [function, hook(MAP.lookup), klabel(Map:lookup), symbol]
  syntax KItem ::= Map "[" KItem "]" "orDefault" KItem      [function, total, hook(MAP.lookupOrDefault), klabel(Map:lookupOrDefault)]
  syntax Map ::= Map "[" key: KItem "<-" value: KItem "]"           [function, total, klabel(Map:update), symbol, hook(MAP.update), prefer]
  syntax Map ::= Map "[" KItem "<-" "undef" "]"     [function, total, hook(MAP.remove), klabel(_[_<-undef]), symbol]
  syntax Map ::= Map "-Map" Map                 [function, total, hook(MAP.difference), latex({#1}-_{\it Map}{#2})]
  syntax Map ::= updateMap(Map, Map)            [function, total, hook(MAP.updateAll)]
  syntax Map ::= removeAll(Map, Set)            [function, total, hook(MAP.removeAll)]
  syntax Set ::= keys(Map)                      [function, total, hook(MAP.keys)]
  syntax List ::= "keys_list" "(" Map ")"       [function, hook(MAP.keys_list)]
  syntax Bool ::= KItem "in_keys" "(" Map ")"       [function, total, hook(MAP.in_keys)]
  syntax List ::= values(Map)                   [function, hook(MAP.values)]
  syntax Int ::= size(Map)                      [function, total, hook(MAP.size), klabel(sizeMap)]
  syntax Bool ::= Map "<=Map" Map               [function, total, hook(MAP.inclusion)]
  syntax KItem ::= choice(Map)                      [function, hook(MAP.choice), klabel(Map:choice)]
endmodule


module MAP-KORE-SYMBOLIC [kore,symbolic,haskell]
  imports MAP
  imports private K-EQUAL
  imports private BOOL

  rule #Ceil(@M:Map [@K:KItem]) => {(@K in_keys(@M)) #Equals true} #And #Ceil(@M) #And #Ceil(@K) [simplification]

  // Symbolic update

  // Adding the definedness condition `notBool (K in_keys(M))` in the ensures clause of the following rule would be redundant
  // because K also appears in the rhs, preserving the case when it's #Bottom.
  rule (K |-> _ M:Map) [ K <- V ] => (K |-> V M) [simplification]
  rule M:Map [ K <- V ] => (K |-> V M) requires notBool (K in_keys(M)) [simplification]
  rule M:Map [ K <- _ ] [ K <- V ] => M [ K <- V ] [simplification]
  // Adding the definedness condition `notBool (K1 in_keys(M))` in the ensures clause of the following rule would be redundant
  // because K1 also appears in the rhs, preserving the case when it's #Bottom.
  rule (K1 |-> V1 M:Map) [ K2 <- V2 ] => (K1 |-> V1 (M [ K2 <- V2 ])) requires K1 =/=K K2 [simplification]

  // Symbolic remove
  rule (K |-> _ M:Map) [ K <- undef ] => M ensures notBool (K in_keys(M)) [simplification]
  rule M:Map [ K <- undef ] => M requires notBool (K in_keys(M)) [simplification]
  // Adding the definedness condition `notBool (K1 in_keys(M))` in the ensures clause of the following rule would be redundant
  // because K1 also appears in the rhs, preserving the case when it's #Bottom.
  rule (K1 |-> V1 M:Map) [ K2 <- undef ] => (K1 |-> V1 (M [ K2 <- undef ])) requires K1 =/=K K2 [simplification]

  // Symbolic lookup
  rule (K  |->  V M:Map) [ K ]  => V ensures notBool (K in_keys(M)) [simplification]
  rule (K1 |-> _V M:Map) [ K2 ] => M [K2] requires K1 =/=K K2 ensures notBool (K1 in_keys(M)) [simplification]
  rule (_MAP:Map [ K  <-  V1 ]) [ K ]  => V1 [simplification]
  rule ( MAP:Map [ K1 <- _V1 ]) [ K2 ] => MAP [ K2 ] requires K1 =/=K K2 [simplification]

  rule (K  |->  V M:Map) [  K ] orDefault _ => V ensures notBool (K in_keys(M)) [simplification]
  rule (K1 |-> _V M:Map) [ K2 ] orDefault D => M [K2] orDefault D requires K1 =/=K K2 ensures notBool (K1 in_keys(M)) [simplification]
  rule (_MAP:Map [ K  <-  V1 ]) [ K ] orDefault _ => V1 [simplification]
  rule ( MAP:Map [ K1 <- _V1 ]) [ K2 ] orDefault D => MAP [ K2 ] orDefault D requires K1 =/=K K2 [simplification]
  rule .Map [ _ ] orDefault D => D [simplification]

  // Symbolic in_keys
  rule K in_keys(_M [ K <- undef ]) => false [simplification]
  rule K in_keys(_M [ K <- _ ]) => true [simplification]
  rule K1 in_keys(M [ K2 <- _ ]) => true requires K1 ==K K2 orBool K1 in_keys(M) [simplification]
  rule K1 in_keys(M [ K2 <- _ ]) => K1 in_keys(M) requires K1 =/=K K2 [simplification]

  rule {false #Equals @Key in_keys(.Map)} => #Ceil(@Key) [simplification]
  rule {@Key in_keys(.Map) #Equals false} => #Ceil(@Key) [simplification]
  rule {false #Equals @Key in_keys(Key' |-> Val @M)} => #Ceil(@Key) #And #Ceil(Key' |-> Val @M) #And #Not({@Key #Equals Key'}) #And {false #Equals @Key in_keys(@M)} [simplification]
  rule {@Key in_keys(Key' |-> Val @M) #Equals false} => #Ceil(@Key) #And #Ceil(Key' |-> Val @M) #And #Not({@Key #Equals Key'}) #And {@Key in_keys(@M) #Equals false} [simplification]

/*
// The rule below is automatically generated by the frontend for every sort
// hooked to MAP.Map. It is left here to serve as documentation.

  rule #Ceil(@M:Map (@K:KItem |-> @V:KItem)) => {(@K in_keys(@M)) #Equals false} #And #Ceil(@M) #And #Ceil(@K) #And #Ceil(@V)
    [simplification]
*/
endmodule


module MAP-SYMBOLIC
  imports MAP-KORE-SYMBOLIC
endmodule


module RANGEMAP
  imports private BOOL-SYNTAX
  imports private INT-SYNTAX
  imports private LIST
  imports private SET

  syntax Range ::= "[" KItem "," KItem ")"    [klabel(Rangemap:Range), symbol]

  syntax RangeMap [hook(RANGEMAP.RangeMap)]
  syntax RangeMap ::= RangeMap RangeMap                        [left, function, hook(RANGEMAP.concat), klabel(_RangeMap_), symbol, assoc, comm, unit(.RangeMap), element(_r|->_), index(0), format(%1%n%2)]
  syntax RangeMap ::= ".RangeMap"                         [function, total, hook(RANGEMAP.unit), klabel(.RangeMap), symbol, latex(\dotCt{RangeMap})]
  syntax RangeMap ::= Range "r|->" KItem                      [function, hook(RANGEMAP.elementRng), klabel(_r|->_), symbol, latex({#1}\mapsto{#2}), injective]

  syntax priorities _r|->_ > _RangeMap_ .RangeMap
  syntax non-assoc _r|->_

  syntax KItem ::= RangeMap "[" KItem "]"                    [function, hook(RANGEMAP.lookup), klabel(RangeMap:lookup), symbol]
  syntax KItem ::= RangeMap "[" KItem "]" "orDefault" KItem      [function, total, hook(RANGEMAP.lookupOrDefault), klabel(RangeMap:lookupOrDefault)]
  syntax Range ::= "find_range" "(" RangeMap "," KItem ")"                    [function, hook(RANGEMAP.find_range), klabel(RangeMap:find_range)]
  syntax RangeMap ::= RangeMap "[" keyRange: Range "<-" value: KItem "]"           [function, klabel(RangeMap:update), symbol, hook(RANGEMAP.updateRng), prefer]
  syntax RangeMap ::= RangeMap "[" Range "<-" "undef" "]"     [function, hook(RANGEMAP.removeRng), klabel(_r[_<-undef]), symbol]
  syntax RangeMap ::= RangeMap "-RangeMap" RangeMap                 [function, total, hook(RANGEMAP.difference), latex({#1}-_{\it RangeMap}{#2})]
  syntax RangeMap ::= updateRangeMap(RangeMap, RangeMap)            [function, total, hook(RANGEMAP.updateAll)]
  syntax RangeMap ::= removeAll(RangeMap, Set)            [function, hook(RANGEMAP.removeAll)]
  syntax Set ::= keys(RangeMap)                      [function, total, hook(RANGEMAP.keys)]
  syntax List ::= "keys_list" "(" RangeMap ")"       [function, hook(RANGEMAP.keys_list)]
  syntax Bool ::= KItem "in_keys" "(" RangeMap ")"       [function, total, hook(RANGEMAP.in_keys)]
  syntax List ::= values(RangeMap)                   [function, hook(RANGEMAP.values)]
  syntax Int ::= size(RangeMap)                      [function, total, hook(RANGEMAP.size), klabel(sizeRangeMap)]
  syntax Bool ::= RangeMap "<=RangeMap" RangeMap               [function, total, hook(RANGEMAP.inclusion)]
  syntax KItem ::= choice(RangeMap)                      [function, hook(RANGEMAP.choice), klabel(RangeMap:choice)]
endmodule


module SET
  imports private INT-SYNTAX
  imports private BASIC-K

  syntax Set [hook(SET.Set)]
  syntax Set ::= Set Set                  [left, function, hook(SET.concat), klabel(_Set_), symbol, assoc, comm, unit(.Set), idem, element(SetItem), format(%1%n%2)]
  syntax Set ::= ".Set"                   [function, total, hook(SET.unit), klabel(.Set), symbol, latex(\dotCt{Set})]
  syntax Set ::= SetItem(KItem)               [function, total, hook(SET.element), klabel(SetItem), symbol, injective]
  syntax Set ::= Set "|Set" Set              [left, function, total, hook(SET.union), comm]
  rule S1:Set |Set S2:Set => S1 (S2 -Set S1) [concrete]
  syntax Set ::= intersectSet(Set, Set)   [function, total, hook(SET.intersection), comm]
  syntax Set ::= Set "-Set" Set           [function, total, hook(SET.difference), latex({#1}-_{\it Set}{#2}), klabel(Set:difference), symbol]
  syntax Bool ::= KItem "in" Set              [function, total, hook(SET.in), klabel(Set:in), symbol]
  syntax Bool ::= Set "<=Set" Set         [function, total, hook(SET.inclusion)]
  syntax Int ::= size(Set)                [function, total, hook(SET.size)]
  syntax KItem ::= choice(Set)                [function, hook(SET.choice), klabel(Set:choice)]
endmodule


module SET-KORE-SYMBOLIC [kore,symbolic]
  imports SET
  imports private K-EQUAL
  imports private BOOL

  //Temporarly rule for #Ceil simplification, should be generated in front-end

// Matching for this version not implemented.
  // rule #Ceil(@S1:Set @S2:Set) =>
  //        {intersectSet(@S1, @S2) #Equals .Set} #And #Ceil(@S1) #And #Ceil(@S2)
  //   [simplification]

//simpler version
  rule #Ceil(@S:Set SetItem(@E:KItem)) =>
         {(@E in @S) #Equals false} #And #Ceil(@S) #And #Ceil(@E)
    [simplification]

  // -Set simplifications
  rule S              -Set .Set           => S          [simplification]
  rule .Set           -Set  _             => .Set       [simplification]
  rule SetItem(X)     -Set (S SetItem(X)) => .Set
                               ensures notBool (X in S) [simplification]
  rule S              -Set (S SetItem(X)) => .Set
                               ensures notBool (X in S) [simplification]
  rule (S SetItem(X)) -Set S              => SetItem(X)
                               ensures notBool (X in S) [simplification]
  rule (S SetItem(X)) -Set SetItem(X)     => S
                               ensures notBool (X in S) [simplification]
  // rule SetItem(X)     -Set S              => SetItem(X)
  //                            requires notBool (X in S)  [simplification]
  // rule (S1 SetItem(X)) -Set (S2 SetItem(X))  => S1 -Set S2
  //                             ensures notBool (X in S1)
  //                             andBool notBool (X in S2) [simplification]



  // |Set simplifications
  rule S    |Set .Set => S    [simplification, comm]
  rule S    |Set S    => S    [simplification]

  rule (S SetItem(X)) |Set SetItem(X) => S SetItem(X)
                             ensures notBool (X in S) [simplification, comm]
  // Currently disabled, see runtimeverification/haskell-backend#3301
  // rule (S SetItem(X)) |Set S          => S SetItem(X)
  //                            ensures notBool (X in S) [simplification, comm]

  // intersectSet simplifications
  rule intersectSet(.Set, _   ) => .Set    [simplification, comm]
  rule intersectSet( S  , S   ) =>  S      [simplification]

  rule intersectSet( S SetItem(X), SetItem(X))     => SetItem(X)
                                                        ensures notBool (X in S)      [simplification, comm]
  // Currently disabled, see runtimeverification/haskell-backend#3294
  // rule intersectSet( S SetItem(X) , S)             => S ensures notBool (X in S)      [simplification, comm]
  rule intersectSet( S1 SetItem(X), S2 SetItem(X)) => intersectSet(S1, S2) SetItem(X)
                                                        ensures notBool (X in S1)
                                                        andBool notBool (X in S2)     [simplification]

  // membership simplifications
  rule _E in .Set           => false   [simplification]
  rule E  in (S SetItem(E)) => true
              ensures notBool (E in S) [simplification]

// These two rules would be sound but impose a giant overhead on `in` evaluation:
  // rule E1 in (S SetItem(E2)) => true requires E1 in S
  //                                 ensures notBool (E2 in S) [simplification]
  // rule E1 in (S SetItem(E2)) => E1 in S requires E1 =/=K E2
  //                                 ensures notBool (E2 in S) [simplification]

  rule X in ((SetItem(X) S) |Set  _            ) => true
                                    ensures notBool (X in S) [simplification]
  rule X in ( _             |Set (SetItem(X) S)) => true
                                    ensures notBool (X in S) [simplification]

endmodule


module SET-SYMBOLIC
  imports SET-KORE-SYMBOLIC
endmodule


module LIST
  imports private INT-SYNTAX
  imports private BASIC-K

  syntax List [hook(LIST.List)]
  syntax List ::= List List               [left, function, total, hook(LIST.concat), klabel(_List_), symbol, smtlib(smt_seq_concat), assoc, unit(.List), element(ListItem), format(%1%n%2)]
  syntax List ::= ".List"                 [function, total, hook(LIST.unit), klabel(.List), symbol, smtlib(smt_seq_nil), latex(\dotCt{List})]
  syntax List ::= ListItem(KItem)             [function, total, hook(LIST.element), klabel(ListItem), symbol, smtlib(smt_seq_elem)]
  syntax KItem ::= List "[" Int "]"           [function, hook(LIST.get), klabel(List:get), symbol]
  syntax List ::= List "[" index: Int "<-" value: KItem "]" [function, hook(LIST.update), klabel(List:set)]
  syntax List ::= makeList(length: Int, value: KItem) [function, hook(LIST.make)]
  syntax List ::= updateList(dest: List, index: Int, src: List) [function, hook(LIST.updateAll)]
  syntax List ::= fillList(List, index: Int, length: Int, value: KItem) [function, hook(LIST.fill)]
  syntax List ::= range(List, fromFront: Int, fromBack: Int)   [function, hook(LIST.range), klabel(List:range), symbol]
  syntax Bool ::= KItem "in" List             [function, total, hook(LIST.in), klabel(_inList_)]
  syntax Int ::= size(List)               [function, total, hook(LIST.size), klabel (sizeList), smtlib(smt_seq_len)]
endmodule


module COLLECTIONS
  imports LIST
  imports SET
  imports MAP

  syntax List ::= Set2List(Set) [function, total, hook(SET.set2list)]
  syntax Set ::= List2Set(List) [function, total, hook(SET.list2set)]

endmodule


module SORT-BOOL
  syntax Bool [hook(BOOL.Bool)]
endmodule


module BOOL-SYNTAX
  imports SORT-BOOL
  syntax Bool ::= "true"  [token]
  syntax Bool ::= "false" [token]
endmodule


module BOOL-COMMON
  imports private BASIC-K
  imports BOOL-SYNTAX

  syntax Bool ::= "notBool" Bool          [function, total, klabel(notBool_), symbol, smt-hook(not), group(boolOperation), latex(\neg_{\scriptstyle\it Bool}{#1}), hook(BOOL.not)]
                > Bool "andBool" Bool     [function, total, klabel(_andBool_), symbol, left, smt-hook(and), group(boolOperation), latex({#1}\wedge_{\scriptstyle\it Bool}{#2}), hook(BOOL.and)]
                | Bool "andThenBool" Bool [function, total, klabel(_andThenBool_), symbol, left, smt-hook(and), group(boolOperation), hook(BOOL.andThen)]
                | Bool "xorBool" Bool     [function, total, klabel(_xorBool_), symbol, left, smt-hook(xor), group(boolOperation), hook(BOOL.xor)]
                | Bool "orBool" Bool      [function, total, klabel(_orBool_), symbol, left, smt-hook(or), group(boolOperation), latex({#1}\vee_{\scriptstyle\it Bool}{#2}), hook(BOOL.or)]
                | Bool "orElseBool" Bool  [function, total, klabel(_orElseBool_), symbol, left, smt-hook(or), group(boolOperation), hook(BOOL.orElse)]
                | Bool "impliesBool" Bool [function, total, klabel(_impliesBool_), symbol, left, smt-hook(=>), group(boolOperation), hook(BOOL.implies)]
                > left:
                  Bool "==Bool" Bool      [function, total, klabel(_==Bool_), symbol, left, comm, smt-hook(=), hook(BOOL.eq)]
                | Bool "=/=Bool" Bool     [function, total, klabel(_=/=Bool_), symbol, left, comm, smt-hook(distinct), hook(BOOL.ne)]

  rule notBool true => false
  rule notBool false => true

  rule true andBool B:Bool => B:Bool
  rule B:Bool andBool true => B:Bool
  rule false andBool _:Bool => false
  rule _:Bool andBool false => false

  rule true andThenBool K::Bool => K
  rule K::Bool andThenBool true => K
  rule false andThenBool _ => false
  rule _ andThenBool false => false

  rule false xorBool B:Bool => B:Bool
  rule B:Bool xorBool false => B:Bool
  rule B:Bool xorBool B:Bool => false

  rule true orBool _:Bool => true
  rule _:Bool orBool true => true
  rule false orBool B:Bool => B
  rule B:Bool orBool false => B

  rule true orElseBool _ => true
  rule _ orElseBool true => true
  rule false orElseBool K::Bool => K
  rule K::Bool orElseBool false => K

  rule true impliesBool B:Bool => B
  rule false impliesBool _:Bool => true
  rule _:Bool impliesBool true => true
  rule B:Bool impliesBool false => notBool B

  rule B1:Bool =/=Bool B2:Bool => notBool (B1 ==Bool B2)
endmodule


module BOOL-KORE [kore, symbolic]
  imports BOOL-COMMON

  rule {true #Equals notBool @B} => {false #Equals @B} [simplification]
  rule {notBool @B #Equals true} => {@B #Equals false} [simplification]
  rule {false #Equals notBool @B} => {true #Equals @B} [simplification]
  rule {notBool @B #Equals false} => {@B #Equals true} [simplification]

  rule {true #Equals @B1 andBool @B2} => {true #Equals @B1} #And {true #Equals @B2} [simplification]
  rule {@B1 andBool @B2 #Equals true} => {@B1 #Equals true} #And {@B2 #Equals true} [simplification]
  rule {false #Equals @B1 orBool @B2} => {false #Equals @B1} #And {false #Equals @B2} [simplification]
  rule {@B1 orBool @B2 #Equals false} => {@B1 #Equals false} #And {@B2 #Equals false} [simplification]
endmodule


module BOOL
  imports BOOL-COMMON
  imports BOOL-KORE
endmodule


module UNSIGNED-INT-SYNTAX
  syntax Int [hook(INT.Int)]
  syntax Int ::= r"[0-9]+" [prefer, token, prec(2)]
endmodule


module INT-SYNTAX
  imports UNSIGNED-INT-SYNTAX
  syntax Int ::= r"[\\+-]?[0-9]+" [prefer, token, prec(2)]
endmodule


module INT-COMMON
  imports INT-SYNTAX
  imports private BOOL

  syntax Int ::= "~Int" Int                     [function, klabel(~Int_), symbol, total, latex(\mathop{\sim_{\scriptstyle\it Int}}{#1}), hook(INT.not), smtlib(notInt)]
               > left:
                 Int "^Int" Int                 [function, klabel(_^Int_), symbol, left, smt-hook(^), latex({#1}\mathrel{{\char`\^}_{\!\scriptstyle\it Int}}{#2}), hook(INT.pow)]
               | Int "^%Int" Int Int            [function, klabel(_^%Int__), symbol, left, smt-hook((mod (^ #1 #2) #3)), hook(INT.powmod)]
               > left:
                 Int "*Int" Int                 [function, total, klabel(_*Int_), symbol, left, comm, smt-hook(*), latex({#1}\mathrel{\ast_{\scriptstyle\it Int}}{#2}), hook(INT.mul)]
               /* FIXME: translate /Int and %Int into smtlib */
               /* /Int and %Int implement t-division, which rounds towards 0 */
               | Int "/Int" Int                 [function, klabel(_/Int_), symbol, left, smt-hook(div), latex({#1}\mathrel{\div_{\scriptstyle\it Int}}{#2}), hook(INT.tdiv)]
               | Int "%Int" Int                 [function, klabel(_%Int_), symbol, left, smt-hook(mod), latex({#1}\mathrel{\%_{\scriptstyle\it Int}}{#2}), hook(INT.tmod)]
               /* divInt and modInt implement e-division according to the Euclidean division theorem, therefore the remainder is always positive */
               | Int "divInt" Int               [function, klabel(_divInt_), symbol, left, smt-hook(div), hook(INT.ediv)]
               | Int "modInt" Int               [function, klabel(_modInt_), symbol, left, smt-hook(mod), hook(INT.emod)]
               > left:
                 Int "+Int" Int                 [function, total, klabel(_+Int_), symbol, left, comm, smt-hook(+), latex({#1}\mathrel{+_{\scriptstyle\it Int}}{#2}), hook(INT.add)]
               | Int "-Int" Int                 [function, total, klabel(_-Int_), symbol, left, smt-hook(-), latex({#1}\mathrel{-_{\scriptstyle\it Int}}{#2}), hook(INT.sub)]
               > left:
                 Int ">>Int" Int                [function, klabel(_>>Int_), symbol, left, latex({#1}\mathrel{\gg_{\scriptstyle\it Int}}{#2}), hook(INT.shr), smtlib(shrInt)]
               | Int "<<Int" Int                [function, klabel(_<<Int_), symbol, left, latex({#1}\mathrel{\ll_{\scriptstyle\it Int}}{#2}), hook(INT.shl), smtlib(shlInt)]
               > left:
                 Int "&Int" Int                 [function, total, klabel(_&Int_), symbol, left, comm, latex({#1}\mathrel{\&_{\scriptstyle\it Int}}{#2}), hook(INT.and), smtlib(andInt)]
               > left:
                 Int "xorInt" Int               [function, total, klabel(_xorInt_), symbol, left, comm, latex({#1}\mathrel{\oplus_{\scriptstyle\it Int}}{#2}), hook(INT.xor), smtlib(xorInt)]
               > left:
                 Int "|Int" Int                 [function, total, klabel(_|Int_), symbol, left, comm, latex({#1}\mathrel{|_{\scriptstyle\it Int}}{#2}), hook(INT.or), smtlib(orInt)]

  syntax Int ::= "minInt" "(" Int "," Int ")"   [function, total, smt-hook((ite (< #1 #2) #1 #2)), hook(INT.min)]
               | "maxInt" "(" Int "," Int ")"   [function, total, smt-hook((ite (< #1 #2) #2 #1)), hook(INT.max)]

  syntax Int ::= absInt ( Int )                 [function, total, smt-hook((ite (< #1 0) (- 0 #1) #1)), hook(INT.abs)]

  syntax Int ::= log2Int ( Int )                [function, hook(INT.log2)]

  syntax Int ::= bitRangeInt           ( Int, index: Int, length: Int ) [function, hook(INT.bitRange)]
               | signExtendBitRangeInt ( Int, index: Int, length: Int ) [function, hook(INT.signExtendBitRange)]

  syntax Bool ::= Int "<=Int" Int         [function, total, klabel(_<=Int_), symbol, smt-hook(<=), latex({#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}), hook(INT.le)]
                | Int "<Int" Int          [function, total, klabel(_<Int_), symbol, smt-hook(<), latex({#1}\mathrel{<_{\scriptstyle\it Int}}{#2}), hook(INT.lt)]
                | Int ">=Int" Int         [function, total, klabel(_>=Int_), symbol, smt-hook(>=), latex({#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}), hook(INT.ge)]
                | Int ">Int" Int          [function, total, klabel(_>Int_), symbol, smt-hook(>), latex({#1}\mathrel{>_{\scriptstyle\it Int}}{#2}), hook(INT.gt)]
                | Int "==Int" Int         [function, total, klabel(_==Int_), symbol, comm, smt-hook(=), latex({#1}\mathrel{{=}{=}_{\scriptstyle\it Int}}{#2}), hook(INT.eq)]
                | Int "=/=Int" Int        [function, total, klabel(_=/=Int_), symbol, comm, smt-hook(distinct), latex({#1}\mathrel{{=}{/}{=}_{\scriptstyle\it Int}}{#2}), hook(INT.ne)]

  syntax Bool ::= Int "dividesInt" Int    [function]

  syntax Int ::= randInt(Int) [function, hook(INT.rand), impure]
  syntax K ::= srandInt(Int) [function, hook(INT.srand), impure]

endmodule


module INT-SYMBOLIC [symbolic]
  imports INT-COMMON
  imports INT-SYMBOLIC-KORE
  imports private BOOL

  // Arithmetic Normalization
  rule I +Int 0 => I [simplification]
  rule I -Int 0 => I [simplification]

  rule X modInt N => X requires 0 <=Int X andBool X <Int N [simplification]
  rule X   %Int N => X requires 0 <=Int X andBool X <Int N [simplification]

  // Bit-shifts
  rule X <<Int 0 => X [simplification]
  rule 0 <<Int _ => 0 [simplification]
  rule X >>Int 0 => X [simplification]
  rule 0 >>Int _ => 0 [simplification]
endmodule


module INT-SYMBOLIC-KORE [symbolic, kore, haskell]
  imports INT-COMMON
  imports ML-SYNTAX
  imports private BOOL

  // Definability Conditions
  rule #Ceil(@I1:Int /Int   @I2:Int) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
  rule #Ceil(@I1:Int %Int   @I2:Int) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
  rule #Ceil(@I1:Int modInt @I2:Int) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
  rule #Ceil(@I1:Int >>Int  @I2:Int) => {(@I2 >=Int 0)  #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]
  rule #Ceil(@I1:Int <<Int  @I2:Int) => {(@I2 >=Int 0)  #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [simplification]

  // Arithmetic Normalization
  rule I +Int B => B +Int I          [concrete(I), symbolic(B), simplification(51)]
  rule A -Int I => A +Int (0 -Int I) [concrete(I), symbolic(A), simplification(51)]

  rule (A +Int I2) +Int I3 => A +Int (I2 +Int I3) [concrete(I2, I3), symbolic(A), simplification]
  rule I1 +Int (B +Int I3) => B +Int (I1 +Int I3) [concrete(I1, I3), symbolic(B), simplification]
  rule I1 -Int (B +Int I3) => (I1 -Int I3) -Int B [concrete(I1, I3), symbolic(B), simplification]
  rule I1 +Int (I2 +Int C) => (I1 +Int I2) +Int C [concrete(I1, I2), symbolic(C), simplification]
  rule I1 +Int (I2 -Int C) => (I1 +Int I2) -Int C [concrete(I1, I2), symbolic(C), simplification]
  rule (I1 -Int B) +Int I3 => (I1 +Int I3) -Int B [concrete(I1, I3), symbolic(B), simplification]
  rule I1 -Int (I2 +Int C) => (I1 -Int I2) -Int C [concrete(I1, I2), symbolic(C), simplification]
  rule I1 -Int (I2 -Int C) => (I1 -Int I2) +Int C [concrete(I1, I2), symbolic(C), simplification]
  rule (C -Int I2) -Int I3 => C -Int (I2 +Int I3) [concrete(I2, I3), symbolic(C), simplification]

  rule I1 &Int (I2 &Int C) => (I1 &Int I2) &Int C [concrete(I1, I2), symbolic(C), simplification]

endmodule


module INT-KORE [kore, symbolic]
  imports private K-EQUAL
  imports private BOOL
  imports INT-COMMON

  rule I1:Int ==K I2:Int => I1 ==Int I2 [simplification]
  rule {K1 ==Int K2 #Equals true} => {K1 #Equals K2} [simplification]
  rule {true #Equals K1 ==Int K2} => {K1 #Equals K2} [simplification]
  rule {K1 ==Int K2 #Equals false} => #Not({K1 #Equals K2}) [simplification]
  rule {false #Equals K1 ==Int K2} => #Not({K1 #Equals K2}) [simplification]
  rule {K1 =/=Int K2 #Equals true} => #Not({K1 #Equals K2}) [simplification]
  rule {true #Equals K1 =/=Int K2} => #Not({K1 #Equals K2}) [simplification]
  rule {K1 =/=Int K2 #Equals false} => {K1 #Equals K2} [simplification]
  rule {false #Equals K1 =/=Int K2} => {K1 #Equals K2} [simplification]

endmodule


module INT
  imports INT-COMMON
  imports INT-SYMBOLIC
  imports INT-KORE
  imports private K-EQUAL
  imports private BOOL

  rule bitRangeInt(I::Int, IDX::Int, LEN::Int) => (I >>Int IDX) modInt (1 <<Int LEN)

  rule signExtendBitRangeInt(I::Int, IDX::Int, LEN::Int) => (bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int 1))) modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))

  rule I1:Int divInt I2:Int => (I1 -Int (I1 modInt I2)) /Int I2
  requires I2 =/=Int 0
  rule
    I1:Int modInt I2:Int
  =>
    ((I1 %Int absInt(I2)) +Int absInt(I2)) %Int absInt(I2)
  requires I2 =/=Int 0    [concrete, simplification]

  rule minInt(I1:Int, I2:Int) => I1 requires I1 <=Int I2
  rule minInt(I1:Int, I2:Int) => I2 requires I1 >=Int I2

  rule I1:Int =/=Int I2:Int => notBool (I1 ==Int I2)
  rule (I1:Int dividesInt I2:Int) => (I2 %Int I1) ==Int 0

  syntax Int ::= freshInt(Int)    [freshGenerator, function, total, private]
  rule freshInt(I:Int) => I
endmodule


module FLOAT-SYNTAX
  syntax Float [hook(FLOAT.Float)]
  syntax Float ::= r"([\\+-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+-]?[0-9]+)?([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(1)]
  syntax Float ::= r"[\\+-]?Infinity([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(3)]
  syntax Float ::= r"NaN([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(3)]
endmodule


module FLOAT
  imports FLOAT-SYNTAX
  imports private BOOL
  imports private INT-SYNTAX

  syntax Int ::= precisionFloat(Float) [function, total, hook(FLOAT.precision)]

  syntax Int ::= exponentBitsFloat(Float) [function, total, hook(FLOAT.exponentBits)]

  syntax Int ::= exponentFloat(Float) [function, total, hook(FLOAT.exponent)]

  syntax Bool ::= signFloat(Float)      [function, total, hook(FLOAT.sign)]

  syntax Bool ::= isNaN(Float)          [function, total, smt-hook(fp.isNaN), hook(FLOAT.isNaN)]
                | isInfinite(Float)     [function, total]

  syntax Float ::= "--Float" Float             [function, total, smt-hook(fp.neg), hook(FLOAT.neg)]
                 > Float "^Float" Float        [function, left, latex({#1}^{#2}), hook(FLOAT.pow)]
                 > left:
                   Float "*Float" Float        [function, left, smt-hook((fp.mul roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}), hook(FLOAT.mul)]
                 | Float "/Float" Float        [function, left, smt-hook((fp.div roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}), hook(FLOAT.div)]
                 | Float "%Float" Float        [function, left, smt-hook((fp.rem roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}), hook(FLOAT.rem)]
                 > left:
                   Float "+Float" Float        [function, left, smt-hook((fp.add roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{+_{\scriptstyle\it Float}}{#2}), hook(FLOAT.add)]
                 | Float "-Float" Float        [function, left, smt-hook((fp.sub roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{-_{\scriptstyle\it Float}}{#2}), hook(FLOAT.sub)]

  syntax Float ::= rootFloat(Float, Int)        [function, hook(FLOAT.root)]
                 | absFloat(Float)              [function, total, smt-hook(fp.abs), hook(FLOAT.abs)]
                 | roundFloat(Float, precision: Int, exponentBits: Int)  [function, hook(FLOAT.round)]
                 | floorFloat(Float)            [function, total, hook(FLOAT.floor)]
                 | ceilFloat(Float)             [function, total, hook(FLOAT.ceil)]
                 | truncFloat(Float)            [function, total, hook(FLOAT.trunc)]
                 | expFloat(Float)              [function, total, hook(FLOAT.exp)]
                 | logFloat(Float)              [function, hook(FLOAT.log)]
                 | sinFloat(Float)              [function, total, hook(FLOAT.sin)]
                 | cosFloat(Float)              [function, total, hook(FLOAT.cos)]
                 | tanFloat(Float)              [function, hook(FLOAT.tan)]
                 | asinFloat(Float)             [function, hook(FLOAT.asin)]
                 | acosFloat(Float)             [function, hook(FLOAT.acos)]
                 | atanFloat(Float)             [function, total, hook(FLOAT.atan)]
                 | atan2Float(Float, Float)     [function, hook(FLOAT.atan2)]
                 | maxFloat(Float, Float)       [function, smt-hook(fp.max), hook(FLOAT.max)]
                 | minFloat(Float, Float)       [function, smt-hook(fp.min), hook(FLOAT.min)]
                 | sqrtFloat(Float)             [function]
                 | maxValueFloat(precision: Int, exponentBits: Int)      [function, hook(FLOAT.maxValue)]
                 | minValueFloat(precision: Int, exponentBits: Int)      [function, hook(FLOAT.minValue)]

  syntax Bool ::= Float "<=Float" Float       [function, smt-hook(fp.leq), latex({#1}\mathrel{\leq_{\scriptstyle\it Float}}{#2}), hook(FLOAT.le)]
                | Float "<Float" Float        [function, smt-hook(fp.lt), latex({#1}\mathrel{<_{\scriptstyle\it Float}}{#2}), hook(FLOAT.lt)]
                | Float ">=Float" Float       [function, smt-hook(fp.geq), latex({#1}\mathrel{\geq_{\scriptstyle\it Float}}{#2}), hook(FLOAT.ge)]
                | Float ">Float" Float        [function, smt-hook(fg.gt), latex({#1}\mathrel{>_{\scriptstyle\it Float}}{#2}), hook(FLOAT.gt)]
                | Float "==Float" Float       [function, comm, smt-hook(fp.eq), latex({#1}\mathrel{==_{\scriptstyle\it Float}}{#2}), hook(FLOAT.eq), klabel(_==Float_)]
                | Float "=/=Float" Float      [function, comm, smt-hook((not (fp.eq #1 #2))), latex({#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2})]

  rule F1:Float =/=Float F2:Float => notBool (F1 ==Float F2)

  syntax Float ::= Int2Float(Int, precision: Int, exponentBits: Int)    [function, latex({\\it{}Int2Float}), hook(FLOAT.int2float)]
  syntax Int ::= Float2Int(Float)    [function, total, latex({\\it{}Float2Int}), hook(FLOAT.float2int)]

  rule sqrtFloat(F:Float) => rootFloat(F, 2)

  rule isInfinite(F:Float) => F >Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F)) orBool F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))

endmodule


module STRING-SYNTAX
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"      [token]
endmodule


module STRING-COMMON
  imports STRING-SYNTAX
  imports private INT
  imports private FLOAT-SYNTAX
  imports private K-EQUAL
  imports private BOOL

  syntax String ::= String "+String" String    [function, total, left, latex({#1}+_{\scriptstyle\it String}{#2}), hook(STRING.concat)]

  syntax Int ::= lengthString ( String ) [function, total, hook(STRING.length)]

  syntax String ::= chrChar ( Int )      [function, hook(STRING.chr)]
  syntax Int ::= ordChar ( String )      [function, hook(STRING.ord)]

  syntax String ::= substrString ( String , startIndex: Int , endIndex: Int ) [function, total, hook(STRING.substr)]

  syntax Int ::= findString ( haystack: String , needle: String , index: Int )   [function, hook(STRING.find)]
  syntax Int ::= rfindString ( haystack: String , needle: String , index: Int )  [function, hook(STRING.rfind)]

  syntax Int ::= findChar ( haystack: String , needles: String , index: Int )     [function, hook(STRING.findChar)]
  syntax Int ::= rfindChar ( haystack: String , needles: String , index: Int )    [function, hook(STRING.rfindChar)]

  syntax String ::= Bool2String(Bool) [function, total]
  rule Bool2String(true)  => "true"
  rule Bool2String(false) => "false"

  syntax Bool ::= String2Bool(String) [function]
  rule String2Bool("true")  => true
  rule String2Bool("false") => false

  syntax String ::= Float2String ( Float )              [function, total, hook(STRING.float2string)]
  syntax String ::= Float2String ( Float , format: String )     [function, klabel(FloatFormat), hook(STRING.floatFormat)]
  syntax Float  ::= String2Float ( String )             [function, hook(STRING.string2float)]

  syntax Int    ::= String2Int   ( String )             [function, hook(STRING.string2int)]
  syntax String ::= Int2String   ( Int )                [function, total, hook(STRING.int2string)]
  syntax String ::= Base2String  ( Int , base: Int )          [function, hook(STRING.base2string)]
  syntax Int    ::= String2Base  ( String , base: Int )       [function, hook(STRING.string2base)]

  syntax String ::= "replaceAll" "(" haystack: String "," needle: String "," replacement: String ")"      [function, total, hook(STRING.replaceAll)]
  syntax String ::= "replace" "(" haystack: String "," needle: String "," replacement: String "," times: Int ")" [function, hook(STRING.replace)]
  syntax String ::= "replaceFirst" "(" haystack: String "," needle: String "," replacement: String ")"    [function, total, hook(STRING.replaceFirst)]
  syntax Int ::= "countAllOccurrences" "(" haystack: String "," needle: String ")"            [function, total, hook(STRING.countAllOccurrences)]

  syntax Bool ::= String "==String" String  [function, total, comm, hook(STRING.eq)]
                | String "=/=String" String [function, total, comm, hook(STRING.ne)]
  rule S1:String =/=String S2:String => notBool (S1 ==String S2)

  syntax Bool ::= String  "<String" String [function, total, hook(STRING.lt)]
                | String "<=String" String [function, total, hook(STRING.le)]
                | String  ">String" String [function, total, hook(STRING.gt)]
                | String ">=String" String [function, total, hook(STRING.ge)]

  syntax String ::= categoryChar(String)       [function, hook(STRING.category)]
                  | directionalityChar(String) [function, hook(STRING.directionality)]

  syntax String ::= "newUUID" [function, hook(STRING.uuid), impure]

  rule S1:String <=String S2:String => notBool (S2 <String S1)
  rule S1:String >String S2:String => S2 <String S1
  rule S1:String >=String S2:String => notBool (S1 <String S2)

  rule findChar(S1:String, S2:String, I:Int) => #if findString(S1, substrString(S2, 0, 1), I) ==Int -1 #then findChar(S1, substrString(S2, 1, lengthString(S2)), I) #else #if findChar(S1, substrString(S2, 1, lengthString(S2)), I) ==Int -1 #then findString(S1, substrString(S2, 0, 1), I) #else minInt(findString(S1, substrString(S2, 0, 1), I), findChar(S1, substrString(S2, 1, lengthString(S2)), I)) #fi #fi requires S2 =/=String ""
  rule findChar(_, "", _) => -1
  rule rfindChar(S1:String, S2:String, I:Int) => maxInt(rfindString(S1, substrString(S2, 0, 1), I), rfindChar(S1, substrString(S2, 1, lengthString(S2)), I)) requires S2 =/=String ""
  rule rfindChar(_, "", _) => -1

  rule countAllOccurrences(Source:String, ToCount:String) => 0
            requires findString(Source, ToCount, 0) <Int 0
  rule countAllOccurrences(Source:String, ToCount:String) => 1 +Int countAllOccurrences(substrString(Source, findString(Source, ToCount, 0) +Int lengthString(ToCount), lengthString(Source)), ToCount)
            requires findString(Source, ToCount, 0) >=Int 0

  rule replaceFirst(Source:String, ToReplace:String, Replacement:String) => substrString(Source, 0, findString(Source, ToReplace, 0))
                +String Replacement +String substrString(Source, findString(Source, ToReplace, 0) +Int lengthString(ToReplace), lengthString(Source))
                requires findString(Source, ToReplace, 0) >=Int 0
  rule replaceFirst(Source:String, ToReplace:String, _:String) => Source
        requires findString(Source, ToReplace, 0) <Int 0


  rule replace(Source:String, ToReplace:String, Replacement:String, Count:Int) =>
       substrString(Source, 0, findString(Source, ToReplace, 0)) +String Replacement +String
       replace(substrString(Source, findString(Source, ToReplace, 0) +Int lengthString(ToReplace), lengthString(Source)), ToReplace, Replacement, Count -Int 1)
        requires Count >Int 0
  rule replace(Source:String, _, _, 0) => Source
  rule replaceAll(Source:String, ToReplace:String, Replacement:String) => replace(Source, ToReplace, Replacement, countAllOccurrences(Source, ToReplace))

endmodule


module STRING-KORE [kore, symbolic]
  imports private K-EQUAL
  imports STRING-COMMON

  rule S1:String ==K S2:String => S1 ==String S2 [simplification]

endmodule


module STRING
  imports STRING-COMMON
  imports STRING-KORE
endmodule


module STRING-BUFFER-IN-K [symbolic]
  imports private BASIC-K
  imports STRING

  syntax StringBuffer ::= ".StringBuffer" [function, total]
  syntax StringBuffer ::= StringBuffer "+String" String [function, total, avoid]
  syntax StringBuffer ::= String
  syntax String ::= StringBuffer2String ( StringBuffer ) [function, total]

  rule {SB:String +String S:String}<:StringBuffer => (SB +String S)::String
  rule .StringBuffer => ""
  rule StringBuffer2String(S:String) => S
endmodule


module STRING-BUFFER-HOOKED [concrete]
  imports private BASIC-K
  imports STRING

  syntax StringBuffer [hook(BUFFER.StringBuffer)]
  syntax StringBuffer ::= ".StringBuffer" [function, total, hook(BUFFER.empty), impure]
  syntax StringBuffer ::= StringBuffer "+String" String [function, total, hook(BUFFER.concat), avoid]
  syntax String ::= StringBuffer2String ( StringBuffer ) [function, total, hook(BUFFER.toString)]
endmodule


module STRING-BUFFER
  imports STRING-BUFFER-HOOKED
  imports STRING-BUFFER-IN-K
endmodule


module BYTES-SYNTAX
  imports private STRING-SYNTAX

  syntax Bytes [hook(BYTES.Bytes)]
  syntax Bytes ::= r"b[\\\"](([\\x20\\x21\\x23-\\x5B\\x5D-\\x7E])|([\\\\][tnfr\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2}))*[\\\"]"      [token]
endmodule


module BYTES-STRING-ENCODE [kore, symbolic]
  imports BYTES-SYNTAX
    syntax String ::= decodeBytes ( encoding: String , contents: Bytes ) [function, hook(BYTES.decodeBytes)]
    syntax Bytes ::= encodeBytes ( encoding: String , contents: String ) [function, hook(BYTES.encodeBytes)]
endmodule


module BYTES-HOOKED
  imports STRING-SYNTAX
  imports BYTES-SYNTAX
  imports BYTES-STRING-ENCODE

  syntax Bytes ::= ".Bytes" [function, total, hook(BYTES.empty)]
  syntax Endianness ::= "LE" [klabel(littleEndianBytes), symbol]
                      | "BE" [klabel(bigEndianBytes), symbol]
  syntax Signedness ::= "Signed" [klabel(signedBytes), symbol]
                      | "Unsigned" [klabel(unsignedBytes), symbol]
  syntax Int ::= Bytes2Int(Bytes, Endianness, Signedness) [function, total, hook(BYTES.bytes2int)]
  syntax Bytes ::= Int2Bytes(length: Int, Int, Endianness) [function, total, hook(BYTES.int2bytes)]
                 | Int2Bytes(Int, Endianness, Signedness) [function, total, klabel(Int2BytesNoLen)]
  syntax String ::= Bytes2String(Bytes) [function, total, hook(BYTES.bytes2string)]
  syntax Bytes ::= String2Bytes(String) [function, total, hook(BYTES.string2bytes)]
  syntax Bytes ::= Bytes "[" index: Int "<-" value: Int "]" [function, hook(BYTES.update)]
  syntax Int ::= Bytes "[" Int "]" [function, hook(BYTES.get)]
  syntax Bytes ::= substrBytes(Bytes, startIndex: Int, endIndex: Int) [function, hook(BYTES.substr)]
  syntax Bytes ::= replaceAtBytes(dest: Bytes, index: Int, src: Bytes) [function, hook(BYTES.replaceAt)]
  syntax Bytes ::= padRightBytes(Bytes, length: Int, value: Int) [function, hook(BYTES.padRight)]
                 | padLeftBytes(Bytes, length: Int, value: Int) [function, hook(BYTES.padLeft)]
  syntax Bytes ::= reverseBytes(Bytes) [function, total, hook(BYTES.reverse)]
  syntax Int ::= lengthBytes(Bytes) [function, total, hook(BYTES.length), smtlib(lengthBytes)]
  syntax Bytes ::= Bytes "+Bytes" Bytes [function, total, hook(BYTES.concat), right]

endmodule


module BYTES-CONCRETE [concrete]
  imports BYTES-HOOKED
endmodule


module BYTES-KORE [kore]
  imports BYTES-HOOKED
  imports BYTES-SYMBOLIC-CEIL
endmodule


module BYTES-SYMBOLIC-CEIL [symbolic, kore]
  imports BYTES-HOOKED
  imports private INT
  imports private BOOL

  rule #Ceil(padRightBytes(_, LEN, VAL)) => {(0 <=Int LEN andBool 0 <=Int VAL andBool VAL <Int 256) #Equals true} [simplification]
  rule #Ceil(padLeftBytes(_, LEN, VAL))  => {(0 <=Int LEN andBool 0 <=Int VAL andBool VAL <Int 256) #Equals true} [simplification]
endmodule


module BYTES
  imports BYTES-CONCRETE
  imports BYTES-KORE
  imports private INT

  rule Int2Bytes(I::Int, E::Endianness, Unsigned) => Int2Bytes((log2Int(I) +Int 8) /Int 8, I, E)
    requires I >Int 0
  rule Int2Bytes(0, _::Endianness, _) => .Bytes
  rule Int2Bytes(I::Int, E::Endianness, Signed) => Int2Bytes((log2Int(I) +Int 9) /Int 8, I, E)
    requires I >Int 0
  rule Int2Bytes(I::Int, E::Endianness, Signed) => Int2Bytes((log2Int(~Int I) +Int 9) /Int 8, I, E)
    requires I <Int -1
  rule Int2Bytes(-1, E::Endianness, Signed) => Int2Bytes(1, -1, E)
endmodule


module ID-SYNTAX-PROGRAM-PARSING
  imports BUILTIN-ID-TOKENS
  syntax Id ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [prec(1), token]
              | #LowerId                                             [token]
              | #UpperId                                             [token]
endmodule


module ID-SYNTAX
  syntax Id [token]
endmodule


module ID-COMMON
  imports ID-SYNTAX
  imports private STRING

  syntax String ::= Id2String ( Id )    [function, total, hook(STRING.token2string)]
  syntax Id ::= String2Id (String) [function, total, hook(STRING.string2token)]
  syntax Id ::= freshId(Int)    [freshGenerator, function, total, private]

  rule freshId(I:Int) => String2Id("_" +String Int2String(I))
endmodule


module ID
  imports ID-COMMON
endmodule


module K-EQUAL-SYNTAX
  imports private BOOL
  imports private BASIC-K

  syntax Bool ::= left:
                  K "==K" K           [function, total, comm, smt-hook(=), hook(KEQUAL.eq), klabel(_==K_), symbol, latex({#1}\mathrel{=_K}{#2}), group(equalEqualK)]
                | K "=/=K" K          [function, total, comm, smt-hook(distinct), hook(KEQUAL.ne), klabel(_=/=K_), symbol, latex({#1}\mathrel{\neq_K}{#2}), group(notEqualEqualK)]

  syntax priorities equalEqualK notEqualEqualK > boolOperation mlOp

  syntax {Sort} Sort ::= "#if" Bool "#then" Sort "#else" Sort "#fi"   [function, total, smt-hook(ite), hook(KEQUAL.ite)]

endmodule


module K-EQUAL-KORE [kore, symbolic]
  import private BOOL
  import K-EQUAL-SYNTAX

  rule K1:Bool ==K K2:Bool => K1 ==Bool K2 [simplification]
  rule {K1 ==K K2 #Equals true} => {K1 #Equals K2} [simplification]
  rule {true #Equals K1 ==K K2} => {K1 #Equals K2} [simplification]
  rule {K1 ==K K2 #Equals false} => #Not({K1 #Equals K2}) [simplification]
  rule {false #Equals K1 ==K K2} => #Not({K1 #Equals K2}) [simplification]
  rule {K1 =/=K K2 #Equals true} => #Not({K1 #Equals K2}) [simplification]
  rule {true #Equals K1 =/=K K2} => #Not({K1 #Equals K2}) [simplification]
  rule {K1 =/=K K2 #Equals false} => {K1 #Equals K2} [simplification]
  rule {false #Equals K1 =/=K K2} => {K1 #Equals K2} [simplification]

endmodule


module K-EQUAL
  import private BOOL
  import K-EQUAL-SYNTAX
  import K-EQUAL-KORE

  rule K1:K =/=K K2:K => notBool (K1 ==K K2)

  rule #if C:Bool #then B1::K #else _ #fi => B1 requires C
  rule #if C:Bool #then _ #else B2::K #fi => B2 requires notBool C

endmodule


module K-REFLECTION
  imports BASIC-K
  imports STRING

  syntax K ::= "#configuration" [function, impure, hook(KREFLECTION.configuration)]
  syntax String ::= #sort(K) [function, hook(KREFLECTION.sort)]
  syntax KItem ::= #fresh(String)   [function, hook(KREFLECTION.fresh), impure]
  syntax KItem ::= getKLabel(K)  [function, hook(KREFLECTION.getKLabel)]

  syntax K ::= #getenv(String) [function, impure, hook(KREFLECTION.getenv)]

  syntax String ::= #kompiledDirectory() [function, hook(KREFLECTION.kompiledDir)]

  // meaningful only for the purposes of compilation to a binary, otherwise
  // undefined
  syntax List ::= #argv() [function, hook(KREFLECTION.argv)]

  // Takes as input a string and returns a K term
  syntax {Sort} Sort ::= #parseKORE(String) [function, hook(KREFLECTION.parseKORE)]
  syntax {Sort} String ::= #unparseKORE(Sort) [function, hook(KREFLECTION.printKORE)]
  syntax IOError ::= "#noParse" "(" String ")" [klabel(#noParse), symbol]

endmodule


module K-IO
  imports private LIST
  imports private STRING
  imports private INT

  syntax IOError ::= "#EOF" [klabel(#EOF), symbol] | #unknownIOError(errno: Int) [symbol]
                   | "#E2BIG" [klabel(#E2BIG), symbol]
                   | "#EACCES" [klabel(#EACCES), symbol]
                   | "#EAGAIN" [klabel(#EAGAIN), symbol]
                   | "#EBADF" [klabel(#EBADF), symbol]
                   | "#EBUSY" [klabel(#EBUSY), symbol]
                   | "#ECHILD" [klabel(#ECHILD), symbol]
                   | "#EDEADLK" [klabel(#EDEADLK), symbol]
                   | "#EDOM" [klabel(#EDOM), symbol]
                   | "#EEXIST" [klabel(#EEXIST), symbol]
                   | "#EFAULT" [klabel(#EFAULT), symbol]
                   | "#EFBIG" [klabel(#EFBIG), symbol]
                   | "#EINTR" [klabel(#EINTR), symbol]
                   | "#EINVAL" [klabel(#EINVAL), symbol]
                   | "#EIO" [klabel(#EIO), symbol]
                   | "#EISDIR" [klabel(#EISDIR), symbol]
                   | "#EMFILE" [klabel(#EMFILE), symbol]
                   | "#EMLINK" [klabel(#EMLINK), symbol]
                   | "#ENAMETOOLONG" [klabel(#ENAMETOOLONG), symbol]
                   | "#ENFILE" [klabel(#ENFILE), symbol]
                   | "#ENODEV" [klabel(#ENODEV), symbol]
                   | "#ENOENT" [klabel(#ENOENT), symbol]
                   | "#ENOEXEC" [klabel(#ENOEXEC), symbol]
                   | "#ENOLCK" [klabel(#ENOLCK), symbol]
                   | "#ENOMEM" [klabel(#ENOMEM), symbol]
                   | "#ENOSPC" [klabel(#ENOSPC), symbol]
                   | "#ENOSYS" [klabel(#ENOSYS), symbol]
                   | "#ENOTDIR" [klabel(#ENOTDIR), symbol]
                   | "#ENOTEMPTY" [klabel(#ENOTEMPTY), symbol]
                   | "#ENOTTY" [klabel(#ENOTTY), symbol]
                   | "#ENXIO" [klabel(#ENXIO), symbol]
                   | "#EPERM" [klabel(#EPERM), symbol]
                   | "#EPIPE" [klabel(#EPIPE), symbol]
                   | "#ERANGE" [klabel(#ERANGE), symbol]
                   | "#EROFS" [klabel(#EROFS), symbol]
                   | "#ESPIPE" [klabel(#ESPIPE), symbol]
                   | "#ESRCH" [klabel(#ESRCH), symbol]
                   | "#EXDEV" [klabel(#EXDEV), symbol]
                   | "#EWOULDBLOCK" [klabel(#EWOULDBLOCK), symbol]
                   | "#EINPROGRESS" [klabel(#EINPROGRESS), symbol]
                   | "#EALREADY" [klabel(#EALREADY), symbol]
                   | "#ENOTSOCK" [klabel(#ENOTSOCK), symbol]
                   | "#EDESTADDRREQ" [klabel(#EDESTADDRREQ), symbol]
                   | "#EMSGSIZE" [klabel(#EMSGSIZE), symbol]
                   | "#EPROTOTYPE" [klabel(#EPROTOTYPE), symbol]
                   | "#ENOPROTOOPT" [klabel(#ENOPROTOOPT), symbol]
                   | "#EPROTONOSUPPORT" [klabel(#EPROTONOSUPPORT), symbol]
                   | "#ESOCKTNOSUPPORT" [klabel(#ESOCKTNOSUPPORT), symbol]
                   | "#EOPNOTSUPP" [klabel(#EOPNOTSUPP), symbol]
                   | "#EPFNOSUPPORT" [klabel(#EPFNOSUPPORT), symbol]
                   | "#EAFNOSUPPORT" [klabel(#EAFNOSUPPORT), symbol]
                   | "#EADDRINUSE" [klabel(#EADDRINUSE), symbol]
                   | "#EADDRNOTAVAIL" [klabel(#EADDRNOTAVAIL), symbol]
                   | "#ENETDOWN" [klabel(#ENETDOWN), symbol]
                   | "#ENETUNREACH" [klabel(#ENETUNREACH), symbol]
                   | "#ENETRESET" [klabel(#ENETRESET), symbol]
                   | "#ECONNABORTED" [klabel(#ECONNABORTED), symbol]
                   | "#ECONNRESET" [klabel(#ECONNRESET), symbol]
                   | "#ENOBUFS" [klabel(#ENOBUFS), symbol]
                   | "#EISCONN" [klabel(#EISCONN), symbol]
                   | "#ENOTCONN" [klabel(#ENOTCONN), symbol]
                   | "#ESHUTDOWN" [klabel(#ESHUTDOWN), symbol]
                   | "#ETOOMANYREFS" [klabel(#ETOOMANYREFS), symbol]
                   | "#ETIMEDOUT" [klabel(#ETIMEDOUT), symbol]
                   | "#ECONNREFUSED" [klabel(#ECONNREFUSED), symbol]
                   | "#EHOSTDOWN" [klabel(#EHOSTDOWN), symbol]
                   | "#EHOSTUNREACH" [klabel(#EHOSTUNREACH), symbol]
                   | "#ELOOP" [klabel(#ELOOP), symbol]
                   | "#EOVERFLOW" [klabel(#EOVERFLOW), symbol]

  syntax IOInt ::= Int | IOError
  syntax IOString ::= String | IOError

  syntax IOInt ::= "#open" "(" path: String ")" [function]
               | "#open" "(" path: String "," mode: String ")" [function, hook(IO.open), impure]

  rule #open(S:String) => #open(S:String, "r+")

  syntax IOInt ::= "#tell" "(" fd: Int ")" [function, hook(IO.tell), impure]
  syntax K ::= "#seek" "(" fd: Int "," index: Int ")" [function, hook(IO.seek), impure]
             | "#seekEnd" "(" fd: Int "," fromEnd: Int ")" [function, hook(IO.seekEnd), impure]

  syntax IOInt ::= "#getc" "(" fd: Int ")"             [function, hook(IO.getc), impure]
  syntax IOString ::= "#read" "(" fd: Int "," length: Int ")"    [function, hook(IO.read), impure]

  syntax K ::= "#putc" "(" fd: Int "," value: Int ")"      [function, hook(IO.putc), impure]
             | "#write" "(" fd: Int "," value: String ")" [function, hook(IO.write), impure]

  syntax K ::= "#close" "(" fd: Int ")" [function, hook(IO.close), impure]

  syntax K ::= "#lock" "(" fd: Int "," endIndex: Int ")" [function, hook(IO.lock), impure]
             | "#unlock" "(" fd: Int "," endIndex: Int ")" [function, hook(IO.unlock), impure]

  syntax IOInt ::= "#accept" "(" fd: Int ")" [function, hook(IO.accept), impure]
  syntax K ::= "#shutdownWrite" "(" fd: Int ")" [function, hook(IO.shutdownWrite), impure]

  syntax Int ::= "#time" "(" ")" [function, hook(IO.time), impure]
  syntax Int ::= "#stdin"   [function, total]
                | "#stdout" [function, total]
                | "#stderr" [function, total]

  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

  syntax KItem ::= #system ( String ) [function, hook(IO.system), impure]
                 | "#systemResult" "(" Int /* exit code */ "," String /* stdout */ "," String /* stderr */ ")" [klabel(#systemResult), symbol]

  syntax IOFile ::= #mkstemp(template: String) [function, hook(IO.mkstemp), impure]
  syntax IOFile ::= IOError
                  | "#tempFile" "(" path: String "," fd: Int ")" [klabel(#tempFile), symbol]

  syntax K ::= #remove(path: String) [function, total, hook(IO.remove), impure]

  syntax K ::= #logToFile(name: String, value: String) [function, total, hook(IO.log), impure, returnsUnit, symbol]
  syntax K ::= #log(value: String) [function, total, hook(IO.logString), impure, returnsUnit, symbol]

  syntax K ::= #trace(value: KItem) [function, total, hook(IO.traceTerm), impure, returnsUnit, symbol]
             | #traceK(value: K)    [function, total, hook(IO.traceTerm), impure, returnsUnit, symbol]

  syntax Stream ::= #buffer(K)
                  | #istream(Int)
                  | #parseInput(String, String)
                  | #ostream(Int)

endmodule

// NOTE: DO NOT DIRECTLY IMPORT *-STREAM MODULES
// These stream modules will be automatically instantiated and implicitly imported
// into the main module when `stream` attributes appear in configuration cells.
// Only `Stream` productions and `[stream]` rules will be imported.
// The cell name will be replaced with the one of the main configuration.

module STDIN-STREAM
  imports K-IO
  imports K-REFLECTION
  imports LIST
  imports INT
  imports BOOL

  configuration <stdin> ListItem(#buffer($STDIN:String)) ListItem($IO:String) ListItem(#istream(#stdin)) </stdin>

  // read one character at a time until we read whitespace
  rule [stdinGetc]:
       <stdin>
       ListItem(#parseInput(_:String, Delimiters:String))
       ListItem(#buffer(S:String => S +String chrChar({#getc(N)}:>Int)))
       ListItem("on")
       ListItem(#istream(N:Int))
       </stdin>
    requires findChar(S, Delimiters, 0) ==Int -1 // [stdin]
       [stream, priority(200)]

  // when we reach whitespace, if it parses create a ListItem
  rule [stdinParseString]:
       <stdin>
       (ListItem(#parseInput("String", Delimiters:String)) => ListItem(S))
       ListItem(#buffer(S:String => ""))
       _:List
       </stdin>
    requires findChar(S, Delimiters, 0) =/=Int -1 // [stdin]
       [stream]

  // a hack: handle the case when we read integers without the help of the IO server
  rule [stdinParseInt]:
       <stdin>
       (ListItem(#parseInput("Int", Delimiters:String))
       => ListItem(String2Int(substrString(S, 0, findChar(S, Delimiters, 0)))))
       ListItem(#buffer(S:String => substrString(S,findChar(S, Delimiters, 0) +Int 1, lengthString(S))))
       _:List
       </stdin>
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool lengthString(S) >Int 1 // [stdin]
       [stream]

  rule [stdinTrim]:
       <stdin>
       ListItem(#parseInput(Sort:String, Delimiters:String))
       ListItem(#buffer(S:String => substrString(S, 1, lengthString(S))))
       _:List
       </stdin>
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool Sort =/=String "String"
       andBool lengthString(S) <=Int 1 // [stdin]
       [stream]

  // NOTE: This unblocking rule will be instantiated and inserted carefully
  // when necessary according to user-defined rules, since otherwise it will
  // lead to a diverging (i.e., non-terminating) transition system definition.
  // Currently, it supports only a simple pattern matching on the top of the
  // input stream cell, e.g.,
  //   rule <k> read() => V ... </k> <in> ListItem(V:Int) => .List ...  </in>
  // Non-supported rules that refer to the input stream cell in a sophisticated
  // way will get stuck in concrete execution mode with real IO enabled (i.e.,
  // under `--io on` option), while they will still work in symbolic execution
  // mode or concrete execution mode with real IO disabled (i.e., under `--io
  // off`, `--search`, or `--debug` options).
  //
  // TODO: More patterns need to be supported as well. In that case, we need to
  // have a way to specify such patterns.
  rule [stdinUnblock]:
       <stdin>
         (.List => ListItem(#parseInput(?Sort:String, ?Delimiters:String)))
         ListItem(#buffer(_:String))
         ...
       </stdin>
       [unblock]

  /*
  syntax Stream ::= "#noIO"

  rule ListItem(#buffer(_))
       (ListItem(#noIO) ListItem(#istream(_:Int)) => .List) [stdin]
  */

endmodule


module STDOUT-STREAM
  imports K-IO
  imports LIST
  imports STRING

  configuration <stdout> ListItem(#ostream(#stdout)) ListItem($IO:String) ListItem(#buffer("")) </stdout>
//configuration <stderr> ListItem(#ostream(#stderr)) ListItem($IO:String) ListItem(#buffer("")) </stderr>

  rule [stdoutBufferFloat]:
       <stdout>
       ListItem(#ostream(_))
       ListItem(_)
       ListItem(#buffer(Buffer:String => Buffer +String Float2String(F)))
       (ListItem(F:Float) => .List)
       _:List
       </stdout>
       // [stdout, stderr]
       [stream, priority(25)]
  rule [stdoutBufferInt]:
       <stdout>
       ListItem(#ostream(_))
       ListItem(_)
       ListItem(#buffer(Buffer:String => Buffer +String Int2String(I)))
       (ListItem(I:Int) => .List)
       _:List
       </stdout>
       // [stdout, stderr]
       [stream, priority(25)]
  rule [stdoutBufferString]:
       <stdout>
       ListItem(#ostream(_))
       ListItem(_)
       ListItem(#buffer(Buffer:String => Buffer +String S))
       (ListItem(S:String) => .List)
       _:List
       </stdout>
       // [stdout, stderr]
       [stream, priority(25)]

  // Send first char from the buffer to the server
  rule [stdoutWrite]:
       <stdout>
       ListItem(#ostream(N:Int => {#write(N, S) ~> N:Int}:>Int))
       ListItem("on")
       ListItem(#buffer(S:String => ""))
       _:List
       </stdout>
    requires S =/=String "" // [stdout, stderr]
       [stream, priority(30)]

  /*
  syntax Stream ::= "#noIO"

  rule ListItem(#buffer(Buffer:String => Buffer +String Float2String(F)))
       (ListItem(F:Float) => .List)
       _:List [stdout, stderr]
  rule ListItem(#buffer(Buffer:String => Buffer +String Int2String(I)))
       (ListItem(I:Int) => .List)
       _:List [stdout, stderr]
  rule ListItem(#buffer(Buffer:String => Buffer +String S))
       (ListItem(S:String) => .List)
       _:List [stdout, stderr]

  rule (ListItem(#ostream(_:Int)) ListItem(#noIO) => .List)
       ListItem(#buffer(_))
       _:List [stdout, stderr]
  */

endmodule


module MINT-SYNTAX
  /*@\section{Description} The MInt implements machine integers of arbitrary
   * bit width represented in 2's complement. */
  syntax {Width} MInt{Width} [hook(MINT.MInt)]

  /*@ Machine integer of bit width and value. */
  syntax {Width} MInt{Width} ::= r"[\\+-]?[0-9]+[pP][0-9]+" [token, prec(2), hook(MINT.literal)]
endmodule


module MINT
  imports MINT-SYNTAX
  imports private INT
  imports private BOOL

  syntax {Width} Int ::= bitwidthMInt(MInt{Width})   [function, total, hook(MINT.bitwidth)]

  syntax {Width} Int ::= MInt2Signed(MInt{Width})     [function, total, hook(MINT.svalue)]
                       | MInt2Unsigned(MInt{Width})     [function, total, hook(MINT.uvalue), smt-hook(bv2int)]

  syntax {Width} MInt{Width} ::= Int2MInt(Int) [function, total, hook(MINT.integer), smt-hook(int2bv)]

  syntax Int ::= sminMInt(Int)    [function]
               | smaxMInt(Int)    [function]
               | uminMInt(Int)    [function]
               | umaxMInt(Int)    [function]
  rule sminMInt(N:Int) => 0 -Int (1 <<Int (N -Int 1))
  rule smaxMInt(N:Int) => (1 <<Int (N -Int 1)) -Int 1
  rule uminMInt(_:Int) => 0
  rule umaxMInt(N:Int) => (1 <<Int N) -Int 1

  syntax Bool ::= soverflowMInt(width: Int, Int)   [function]
                | uoverflowMInt(width: Int, Int)   [function]
  rule
    soverflowMInt(N:Int, I:Int)
  =>
    I <Int sminMInt(N) orBool I >Int smaxMInt(N)
  rule
    uoverflowMInt(N:Int, I:Int)
  =>
    I <Int uminMInt(N) orBool I >Int umaxMInt(N)

  syntax {Width} MInt{Width} ::= "~MInt" MInt{Width} [function, total, hook(MINT.not), smt-hook(bvnot)]
                               | "--MInt" MInt{Width} [function, total, hook(MINT.neg), smt-hook(bvuminus)]
                               > left:
                                 MInt{Width} "*MInt" MInt{Width} [function, total, hook(MINT.mul), smt-hook(bvmul)]
                               | MInt{Width} "/sMInt" MInt{Width} [function, hook(MINT.sdiv), smt-hook(bvsdiv)]
                               | MInt{Width} "%sMInt" MInt{Width} [function, hook(MINT.srem), smt-hook(bvsrem)]
                               | MInt{Width} "/uMInt" MInt{Width} [function, hook(MINT.udiv), smt-hook(bvudiv)]
                               | MInt{Width} "%uMInt" MInt{Width} [function, hook(MINT.urem), smt-hook(bvurem)]
                               > left:
                                 MInt{Width} "+MInt" MInt{Width} [function, total, hook(MINT.add), smt-hook(bvadd)]
                               | MInt{Width} "-MInt" MInt{Width} [function, total, hook(MINT.sub), smt-hook(bvsub)]
                               > left:
                                 MInt{Width} "<<MInt" MInt{Width} [function, hook(MINT.shl), smt-hook(bvshl)]
                               | MInt{Width} ">>aMInt" MInt{Width} [function, hook(MINT.ashr), smt-hook(bvashr)]
                               | MInt{Width} ">>lMInt" MInt{Width} [function, hook(MINT.lshr), smt-hook(bvlshr)]
                               > left:
                                 MInt{Width} "&MInt" MInt{Width} [function, total, hook(MINT.and), smt-hook(bvand)]
                               > left:
                                 MInt{Width} "xorMInt" MInt{Width} [function, total, hook(MINT.xor), smt-hook(bvxor)]
                               > left:
                                 MInt{Width} "|MInt" MInt{Width} [function, total, hook(MINT.or), smt-hook(bvor)]

  syntax {Width} Bool ::= MInt{Width} "<sMInt" MInt{Width} [function, total, hook(MINT.slt), smt-hook(bvslt)]
                        | MInt{Width} "<uMInt" MInt{Width} [function, total, hook(MINT.ult), smt-hook(bvult)]
                        | MInt{Width} "<=sMInt" MInt{Width} [function, total, hook(MINT.sle), smt-hook(bvsle)]
                        | MInt{Width} "<=uMInt" MInt{Width} [function, total, hook(MINT.ule), smt-hook(bvule)]
                        | MInt{Width} ">sMInt" MInt{Width} [function, total, hook(MINT.sgt), smt-hook(bvsgt)]
                        | MInt{Width} ">uMInt" MInt{Width} [function, total, hook(MINT.ugt), smt-hook(bvugt)]
                        | MInt{Width} ">=sMInt" MInt{Width} [function, total, hook(MINT.sge), smt-hook(bvsge)]
                        | MInt{Width} ">=uMInt" MInt{Width} [function, total, hook(MINT.uge), smt-hook(bvuge)]
                        | MInt{Width} "==MInt" MInt{Width} [function, total, hook(MINT.eq), smt-hook(=)]
                        | MInt{Width} "=/=MInt" MInt{Width} [function, total, hook(MINT.ne), smt-hook(distinct)]

  syntax {Width} MInt{Width} ::= sMaxMInt(MInt{Width}, MInt{Width}) [function, total, hook(MINT.smax), smt-hook((ite (bvslt #1 #2) #2 #1))]
                               | sMinMInt(MInt{Width}, MInt{Width}) [function, total, hook(MINT.smin), smt-hook((ite (bvslt #1 #2) #1 #2))]
                               | uMaxMInt(MInt{Width}, MInt{Width}) [function, total, hook(MINT.umax), smt-hook((ite (bvult #1 #2) #2 #1))]
                               | uMinMInt(MInt{Width}, MInt{Width}) [function, total, hook(MINT.umin), smt-hook((ite (bvult #1 #2) #1 #2))]

  syntax {Width1, Width2} MInt{Width1} ::= roundMInt(MInt{Width2}) [function, total, hook(MINT.round)]
endmodule


module STRATEGY
    imports ML-SYNTAX
    imports KVARIABLE-SYNTAX
    imports private K-EQUAL

    syntax #RuleTag ::= #KVariable

    syntax Strategy ::= #STUCK()    [symbol]
                      | "^" #RuleTag [symbol, klabel(#applyRule)]
                      | "~" #RuleTag [symbol, klabel(#appliedRule)]

    configuration <s> $STRATEGY:K </s>
endmodule


module RULE-TAG-SYNTAX
    imports BUILTIN-ID-TOKENS

    syntax #RuleTag ::= #LowerId [token]
endmodule


module DEFAULT-STRATEGY-CONCRETE [concrete]
    imports STRATEGY
    imports RULE-TAG-SYNTAX
    rule ~ regular => ^ regular [anywhere]
endmodule


module DEFAULT-STRATEGY-SYMBOLIC [symbolic]
    imports STRATEGY
    imports RULE-TAG-SYNTAX
    rule <s> ~ regular => ^ regular ... </s>
endmodule


module DEFAULT-STRATEGY
    imports STRATEGY
    imports DEFAULT-STRATEGY-CONCRETE
    imports DEFAULT-STRATEGY-SYMBOLIC

    rule initSCell(_) => <s> ^ regular </s> [priority(25)]
endmodule


module STRATEGY-ABSTRACT
    imports STRATEGY

    syntax #RuleTag ::= "(" #RuleTag ")" [bracket]
 // ----------------------------------------------

    syntax Strategy ::= ".Strategy"
                      | "(" Strategy ")" [bracket]
 // ----------------------------------------------
    rule <s> .Strategy => . ... </s>

    syntax KItem ::= #catchSTUCK ( Strategy )
 // -----------------------------------------
    rule <s> #catchSTUCK(_) => . ... </s>
    rule <s> #STUCK() ~> (_S:Strategy => .) ... </s>
    rule <s> #STUCK() ~> #catchSTUCK(S) => S ... </s>

    syntax Strategy ::= Strategy ";" Strategy [left]
 // ------------------------------------------------
    rule <s> S:Strategy ; S':Strategy => S ~> S' ... </s>

    syntax #RuleTag ::= #RuleTag "|" #RuleTag [left, klabel(#alternateRule)]
 // ------------------------------------------------------------------------
    rule <s> ^ RT:#RuleTag | RT':#RuleTag => ^ RT ~> #catchSTUCK(^ RT') ... </s>

    syntax #RuleTag ::= #RuleTag "*" [klabel(#repeatRule)]
 // ------------------------------------------------------
    rule <s> ^ RT:#RuleTag * => ^ RT ~> ^ RT * ~> #catchSTUCK(.Strategy) ... </s>
endmodule
