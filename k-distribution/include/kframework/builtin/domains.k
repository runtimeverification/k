// Copyright (c) 2015-2019 K Team. All Rights Reserved.
require "kast.k"

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
endmodule

module ARRAY-SYNTAX
  imports LIST

  syntax Array [hook(ARRAY.Array), unit(arrayCtor), element(_[_<-_])]

  syntax KItem ::= Array "[" Int "]" [function, hook(ARRAY.lookup)]
  syntax Array ::= Array "[" key: Int "<-" value: KItem "]" [function, hook(ARRAY.update), klabel(_[_<-_]), symbol]
  syntax Array ::= Array "[" Int "<-" "undef" "]" [function, hook(ARRAY.remove)]
  syntax Array ::= updateArray(Array, Int, List) [function, hook(ARRAY.updateAll)]
  /*@ Sets a range of indices (given by an index into the array and the number
   of indices to set) to the same value. */
  syntax Array ::= fillArray(Array, index: Int, length: Int, value: KItem) [function, hook(ARRAY.fill)]

  syntax Bool ::= Int "in_keys" "(" Array ")" [function, functional, hook(ARRAY.in_keys)]
endmodule

module ARRAY-CONCRETE [concrete, kast]
  imports ARRAY-SYNTAX
  imports LIST
  imports STRING-SYNTAX

  syntax Array ::= makeEmptyArray(Int) [function, hook(ARRAY.makeEmpty), impure]
                 | arrayCtor(String, Int, KItem) [function, hook(ARRAY.ctor), symbol]
                 | makeArray(Int, KItem) [function, hook(ARRAY.make), impure, klabel(makeArrayOcaml)]
endmodule

module ARRAY-SYMBOLIC [symbolic]
  imports ARRAY-IN-K
endmodule

module ARRAY-KORE [kore]
  imports ARRAY-IN-K
endmodule

module ARRAY-IN-K
  imports ARRAY-SYNTAX
  imports LIST
  imports K-EQUAL
  imports INT

  syntax Array ::= makeArray(Int, KItem) [function, hook(ARRAY.make)]

  syntax Array ::= arr(List, Int, KItem)

  rule makeArray(I::Int, D::KItem) => arr(.List, I, D)

  rule arr(L::List, _, D::KItem) [ IDX::Int ] => #if IDX >=Int size(L) #then D #else L[IDX] #fi

  syntax List ::= ensureOffsetList(List, Int, KItem) [function]
  rule ensureOffsetList(L::List, IDX::Int, D::KItem) => #if IDX >=Int size(L) #then updateList(makeList(IDX +Int 1, D), 0, L) #else L #fi

  rule arr(L::List, I::Int, D::KItem) [ IDX::Int <- VAL::KItem ] => arr(ensureOffsetList(L, IDX, D) [ IDX <- VAL ], I, D)

  rule arr(L::List, I::Int, D::KItem) [ IDX::Int <- undef ] => arr(L, I, D) [ IDX <- D ]

  rule updateArray(arr(L::List, I::Int, D::KItem), IDX::Int, L2::List) => arr(updateList(ensureOffsetList(L, IDX +Int size(L2) -Int 1, D), IDX, L2), I, D)

  rule fillArray(arr(L::List, I::Int, D::KItem), IDX::Int, LEN::Int, VAL::KItem) => arr(fillList(ensureOffsetList(L, IDX +Int LEN -Int 1, D), IDX, LEN, VAL), I, D)

  rule IDX::Int in_keys(arr(_, I::Int, _)) => IDX >=Int 0 andBool IDX <Int I
endmodule

module ARRAY
  imports ARRAY-CONCRETE
  imports ARRAY-SYMBOLIC
  imports ARRAY-KORE
endmodule

module MAP
  imports BOOL-SYNTAX
  imports INT-SYNTAX
  imports LIST
  imports SET

  syntax Map [hook(MAP.Map)]

  /*@\section{Description} The Map represents a generalized associative array.
   Each key can be paired with an arbitrary value, and can be used to reference
   its associated value. Multiple bindings for the same key are not allowed. */

  /*@ Construct a new Map consisting of key/value pairs of two Maps (the keys of
   the two Maps are assumed disjoint) */
  syntax Map ::= Map Map                        [left, function, hook(MAP.concat), klabel(_Map_), symbol, assoc, comm, unit(.Map), element(_|->_), index(0), format(%1%n%2)]
  /*@  Construct an empty Map */
  syntax Map ::= ".Map"                         [function, functional, hook(MAP.unit), klabel(.Map), symbol, latex(\dotCt{Map})]
               // breaks klabel uniqueness
               //| "."                            [function, hook(MAP.unit)]
  /*@ Construct a singleton Map (a Map with only one key/value pair). The key
   is on the left and the value is on the right */
  syntax Map ::= KItem "|->" KItem                      [function, functional, hook(MAP.element), klabel(_|->_), symbol, latex({#1}\mapsto{#2})]

  syntax priorities _|->_ > _Map_ .Map
  syntax non-assoc _|->_

  /*@ Retrieve the value associated with the given key */
  syntax KItem ::= Map "[" KItem "]"                    [function, hook(MAP.lookup), klabel(Map:lookup), symbol]

  syntax KItem ::= Map "[" KItem "]" "orDefault" KItem      [function, functional, hook(MAP.lookupOrDefault), klabel(Map:lookupOrDefault)]

  /*@ Update a Map in form of  of keys and values: */
  syntax Map ::= Map "[" key: KItem "<-" value: KItem "]"           [function, functional, klabel(Map:update), symbol, hook(MAP.update), prefer]

  /*@ Remove key/value pair associated with the key from map? */
  syntax Map ::= Map "[" KItem "<-" "undef" "]"     [function, functional, hook(MAP.remove), klabel(_[_<-undef]), symbol]

  /*@ Get the difference of two maps interpreted as sets of entries
   ($M_1 \setminus M2$) */
  syntax Map ::= Map "-Map" Map                 [function, functional, hook(MAP.difference), latex({#1}-_{\it Map}{#2})]

  /*@ Update the first map by adding all key/value pairs in the second map. If a
   key in the first map exists also in the second map, its associated value will
   be overwritten by the value from the second map. */
  syntax Map ::= updateMap(Map, Map)            [function, functional, hook(MAP.updateAll)]

  /*@ Update the Map by removing all key/value pairs with the key in the Set. */
  syntax Map ::= removeAll(Map, Set)            [function, functional, hook(MAP.removeAll)]

  /*@ Get a Set consisting of all keys in the Map:*/
  syntax Set ::= keys(Map)                      [function, functional, hook(MAP.keys)]
  syntax List ::= "keys_list" "(" Map ")"       [function, hook(MAP.keys_list)]

  syntax Bool ::= KItem "in_keys" "(" Map ")"       [function, functional, hook(MAP.in_keys)]

  /*@ Get a List consisting of all values in the Map: */
  syntax List ::= values(Map)                   [function, hook(MAP.values)]

  /*@ Get the Map size (number of key/value pairs) */
  syntax Int ::= size(Map)                      [function, functional, hook(MAP.size), klabel(sizeMap)]

  /*@ Check map inclusion */
  syntax Bool ::= Map "<=Map" Map               [function, functional, hook(MAP.inclusion)]

  /*@ Get an arbitrarily chosen key of the Map  */
  syntax KItem ::= choice(Map)                      [function, hook(MAP.choice), klabel(Map:choice)]
endmodule

module MAP-KORE-SYMBOLIC [kore,symbolic]
  imports MAP

   rule #Ceil(@M:Map [@K:KItem]) => {(@K in_keys(@M)) #Equals true} #And #Ceil(@M) #And #Ceil(@K) [anywhere, simplification]

/*
// The rules below are automatically generated by the frontend.
// They are left here to serve as documentation.

  rule K:KItem in_keys(M:Map K |-> _) => true
  rule K:KItem in_keys(_:Map)         => false [owise]

  rule #Ceil(@M:Map (@K:KItem |-> @V:KItem)) => {(@K in_keys(@M)) #Equals false} #And #Ceil(@M) #And #Ceil(@K) #And #Ceil(@V)
  [anywhere, simplification]
*/
endmodule

module MAP-JAVA-SYMBOLIC [kast, symbolic]
  imports MAP
  imports K-EQUAL
  rule .Map [ K1 <- V1 ] => K1 |-> V1

  rule ((K1 |-> V1) MAP) [ K2 ] => V1         requires K1  ==K K2
  rule ((K1 |-> V1) MAP) [ K2 ] => MAP [ K2 ] requires K1 =/=K K2

  rule (MAP:Map [ K1 <- V1 ]) [ K2 ] => V1         requires K1  ==K K2
  rule (MAP:Map [ K1 <- V1 ]) [ K2 ] => MAP [ K2 ] requires K1 =/=K K2

  rule ((K1 |-> V1) MAP) [ K2 <- V2 ] => (K1 |-> V2) MAP                requires K1  ==K K2
  rule ((K1 |-> V1) MAP) [ K2 <- V2 ] => (K1 |-> V1) (MAP [ K2 <- V2 ]) requires K1 =/=K K2

  rule (MAP:Map [ K1 <- V1 ]) [ K2 <- V2 ] => MAP              [ K1 <- V2 ] requires K1  ==K K2

  // potential infinite loop
  // rule (MAP:Map [ K1 <- V1 ]) [ K2 <- V2 ] => MAP [ K2 <- V2 ] [ K1 <- V1 ] requires K1 =/=K K2

  rule K1 in_keys(M K2 |-> _) => true          requires K1  ==K K2 orBool K1 in_keys(M) [simplification]
  rule K1 in_keys(M K2 |-> _) => K1 in_keys(M) requires K1 =/=K K2 [simplification]

  rule K1 in_keys(M [ K2 <- _ ]) => true          requires K1  ==K K2 orBool K1 in_keys(M) [simplification]
  rule K1 in_keys(M [ K2 <- _ ]) => K1 in_keys(M) requires K1 =/=K K2 [simplification]
endmodule

module MAP-SYMBOLIC
  imports MAP-JAVA-SYMBOLIC
  imports MAP-KORE-SYMBOLIC
endmodule

module SET
  imports INT-SYNTAX
  imports BASIC-K

  syntax Set [hook(SET.Set)]

  /*@ \section{Description} The Set represents a mathematical set (a collection
   of unique items). */

  /*@ Construct a new Set as the union of two different sets ($A \cup B$) */
  syntax Set ::= Set Set                  [left, function, functional, hook(SET.concat), klabel(_Set_), symbol, assoc, comm, unit(.Set), idem, element(SetItem), format(%1%n%2)]
  /*@ Construct an empty Set */
  syntax Set ::= ".Set"                   [function, functional, hook(SET.unit), klabel(.Set), symbol, latex(\dotCt{Set})]
               //| "."
  /*@ Construct a singleton Set (a Set with only one element $\{ a \}$). To add
   an element $a$ to a set $A$, construct the union of the singleton set
   $\{ a \}$ and $A$ ($\{ a \} \cup A$). */
  syntax Set ::= SetItem(KItem)               [function, functional, hook(SET.element), klabel(SetItem), symbol]

  /*@ Get the intersection of two sets ($A \cap B$) */
  syntax Set ::= intersectSet(Set, Set)   [function, functional, hook(SET.intersection)]

  /*@ Get the relative complement of two asets ($A \setminus B$)*/
  syntax Set ::= Set "-Set" Set           [function, functional, hook(SET.difference), latex({#1}-_{\it Set}{#2}), klabel(Set:difference), symbol]

  /*@ Check element membership in a set ($a \in A$) */
  syntax Bool ::= KItem "in" Set              [function, functional, hook(SET.in), klabel(Set:in), symbol]

  /*@ Check set inclusion ($A \subseteq B$) */
  syntax Bool ::= Set "<=Set" Set         [function, functional, hook(SET.inclusion)]

  /*@ Get the cardinality of a set ($|A|$) */
  syntax Int ::= size(Set)                [function, functional, hook(SET.size)]

  /*@ Get an arbitrarily chosen element of the Set */
  syntax KItem ::= choice(Set)                [function, hook(SET.choice), klabel(Set:choice)]
endmodule

module LIST
  imports INT-SYNTAX
  imports BASIC-K

  syntax List [hook(LIST.List)]

  /*@ \section{Description} \K lists are ordered collections that may contain
   duplicate elements. These behave more like lists in functional programming
   languages than arrays in imperative programming languages; there's no
   numerical indexing, but instead specific elements are refered to using the
   Mylist,Mylist construct in combination with the MyListItem construct. It's
   worth noting that \K lists aren't exactly like lists in functional languages;
   they're associative, which means that it's easy to access elements at both
   ends of the lists and concatenate them. For example, L:Mylist,E accesses
   element E at the end of a list. */

  //TODO(AndreiS): move the paragraph below
  /*@ \section{User-Defined Lists} It is very common in \K to define a shorthand
   for lists of user-defined sorts. \K 's builtin way of doing this is to use
   List\{KItem,"Separator"\}, where "Separator" is any valid character or
   sequence of characters used to separate distinct elements.
   For example, after defining \\
   syntax KItem ::= Elt\\
   a user could then define
   syntax Elts ::= List\{Elt,","\} \\
   which would be a comma-separated list whose elements are all of sort Elt. A
   user could just as well define \\
   syntax Elts ::= List\{Elt,"and"\} \\
   which would be a list containing elements of sort Elt that are separated with
   the word "and". If only one argument is given, the separator is asumed to be
   commas. So, \\
   syntax Elts = List\{Elt\} \\
   would define a comma-separated list containing elements of sort Elt.
  */

  /*@ Construct a new List as the concatenation of two Lists. This is similar to
   the append "@" operation in many functional programming languages. */
  syntax List ::= List List               [left, function, functional, hook(LIST.concat), klabel(_List_), symbol, smtlib(smt_seq_concat), assoc, unit(.List), element(ListItem), format(%1%n%2)]
  /*@ Construct an empty List: */
  syntax List ::= ".List"                 [function, functional, hook(LIST.unit), klabel(.List), symbol, smtlib(smt_seq_nil), latex(\dotCt{List})]
                //| "."
  /*@ Construct a singleton List (a list with only  one element) */
  syntax List ::= ListItem(KItem)             [function, functional, hook(LIST.element), klabel(ListItem), symbol, smtlib(smt_seq_elem)]

  /*@ Get an element form the List by index. Positive indices mean from the
   beginning (0 is the first element), and negative indices mean from the end
   (-1 is the last element). */
  syntax KItem ::= List "[" Int "]"           [function, hook(LIST.get), klabel(List:get), symbol]

  syntax List ::= List "[" index: Int "<-" value: KItem "]" [function, hook(LIST.update), klabel(List:set)]

  syntax List ::= makeList(length: Int, value: KItem) [function, hook(LIST.make)]

  syntax List ::= updateList(dest: List, index: Int, src: List) [function, hook(LIST.updateAll)]

  syntax List ::= fillList(List, index: Int, length: Int, value: KItem) [function, hook(LIST.fill)]

  /*@ Remove elements from the beginning and the end of the List. */
  syntax List ::= range(List, fromFront: Int, fromBack: Int)   [function, hook(LIST.range), klabel(List:range), symbol]

  /*@ Check element membership in the given list */
  syntax Bool ::= KItem "in" List             [function, functional, hook(LIST.in), klabel(_inList_)]

  /*@ Get the list length */
  syntax Int ::= size(List)               [function, functional, hook(LIST.size), klabel (sizeList), smtlib(smt_seq_len)]
endmodule

module COLLECTIONS
  imports LIST
  imports SET
  imports MAP

  syntax List ::= Set2List(Set) [function, functional, hook(SET.set2list)]
  syntax Set ::= List2Set(List) [function, functional, hook(SET.list2set)]

endmodule

module BOOL-SYNTAX
  syntax Bool [hook(BOOL.Bool)]
  syntax Bool ::= "true"  [token]
  syntax Bool ::= "false" [token]
endmodule

module BOOL
  imports BASIC-K
  imports BOOL-SYNTAX
  syntax Bool ::= "notBool" Bool          [function, functional, klabel(notBool_), symbol, smt-hook(not), boolOperation, latex(\neg_{\scriptstyle\it Bool}{#1}), hook(BOOL.not)]
                > Bool "andBool" Bool     [function, functional, klabel(_andBool_), symbol, left, smt-hook(and), boolOperation, latex({#1}\wedge_{\scriptstyle\it Bool}{#2}), hook(BOOL.and)]
                | Bool "andThenBool" Bool [function, functional, klabel(_andThenBool_), symbol, left, smt-hook(and), boolOperation, hook(BOOL.andThen)]
                | Bool "xorBool" Bool     [function, functional, klabel(_xorBool_), symbol, left, smt-hook(xor), boolOperation, hook(BOOL.xor)]
                | Bool "orBool" Bool      [function, functional, klabel(_orBool_), left, smt-hook(or), boolOperation, latex({#1}\vee_{\scriptstyle\it Bool}{#2}), hook(BOOL.or)]
                | Bool "orElseBool" Bool  [function, functional, klabel(_orElseBool_), symbol, left, smt-hook(or), boolOperation, hook(BOOL.orElse)]
                | Bool "impliesBool" Bool [function, functional, klabel(_impliesBool_), symbol, left, smt-hook(=>), boolOperation, hook(BOOL.implies)]
                > left:
                  Bool "==Bool" Bool      [function, functional, klabel(_==Bool_), symbol, left, smt-hook(=), hook(BOOL.eq)]
                | Bool "=/=Bool" Bool     [function, functional, klabel(_=/=Bool_), symbol, left, smt-hook(distinct), hook(BOOL.ne)]

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
  imports BOOL
  syntax Int ::= "~Int" Int                     [function, klabel(~Int_), symbol, functional, latex(\mathop{\sim_{\scriptstyle\it Int}}{#1}), hook(INT.not), smtlib(notInt)]
               > left:
                 Int "^Int" Int                 [function, klabel(_^Int_), symbol, left, smt-hook(^), latex({#1}\mathrel{{\char`\^}_{\!\scriptstyle\it Int}}{#2}), hook(INT.pow)]
               | Int "^%Int" Int Int            [function, klabel(_^%Int__), symbol, left, smt-hook((mod (^ #1 #2) #3)), hook(INT.powmod)]
               > left:
                 Int "*Int" Int                 [function, functional, klabel(_*Int_), symbol, left, smt-hook(*), latex({#1}\mathrel{\ast_{\scriptstyle\it Int}}{#2}), hook(INT.mul)]
               /* FIXME: translate /Int and %Int into smtlib */
               /* /Int and %Int implement t-division, which rounds towards 0 */
               | Int "/Int" Int                 [function, klabel(_/Int_), symbol, left, smt-hook(div), latex({#1}\mathrel{\div_{\scriptstyle\it Int}}{#2}), hook(INT.tdiv)]
               | Int "%Int" Int                 [function, klabel(_%Int_), symbol, left, smt-hook(mod), latex({#1}\mathrel{\%_{\scriptstyle\it Int}}{#2}), hook(INT.tmod)]
               /* divInt and modInt implement e-division according to the Euclidian division theorem, therefore the remainder is always positive */
               | Int "divInt" Int               [function, klabel(_divInt_), symbol, left, smt-hook(div), hook(INT.ediv)]
               | Int "modInt" Int               [function, klabel(_modInt_), symbol, left, smt-hook(mod), hook(INT.emod)]
               > left:
                 Int "+Int" Int                 [function, functional, klabel(_+Int_), symbol, left, smt-hook(+), latex({#1}\mathrel{+_{\scriptstyle\it Int}}{#2}), hook(INT.add)]
               | Int "-Int" Int                 [function, functional, klabel(_-Int_), symbol, left, smt-hook(-), latex({#1}\mathrel{-_{\scriptstyle\it Int}}{#2}), hook(INT.sub)]
               > left:
                 Int ">>Int" Int                [function, klabel(_>>Int_), symbol, left, latex({#1}\mathrel{\gg_{\scriptstyle\it Int}}{#2}), hook(INT.shr), smtlib(shrInt)]
               | Int "<<Int" Int                [function, klabel(_<<Int_), symbol, left, latex({#1}\mathrel{\ll_{\scriptstyle\it Int}}{#2}), hook(INT.shl), smtlib(shlInt)]
               > left:
                 Int "&Int" Int                 [function, functional, klabel(_&Int_), symbol, left, latex({#1}\mathrel{\&_{\scriptstyle\it Int}}{#2}), hook(INT.and), smtlib(andInt)]
               > left:
                 Int "xorInt" Int               [function, functional, klabel(_xorInt_), symbol, left, latex({#1}\mathrel{\oplus_{\scriptstyle\it Int}}{#2}), hook(INT.xor), smtlib(xorInt)]
               > left:
                 Int "|Int" Int                 [function, functional, klabel(_|Int_), symbol, left, latex({#1}\mathrel{|_{\scriptstyle\it Int}}{#2}), hook(INT.or), smtlib(orInt)]

  syntax Int ::= "minInt" "(" Int "," Int ")"   [function, functional, smt-hook((ite (< #1 #2) #1 #2)), hook(INT.min)]
               | "maxInt" "(" Int "," Int ")"   [function, functional, smt-hook((ite (< #1 #2) #2 #1)), hook(INT.max)]
               | absInt ( Int )                 [function, functional, smt-hook((ite (< #1 0) (- 0 #1) #1)), hook(INT.abs)]
               | log2Int ( Int )                [function, hook(INT.log2)]

  syntax Int ::= bitRangeInt           ( Int, index: Int, length: Int ) [function, hook(INT.bitRange)]
  syntax Int ::= signExtendBitRangeInt ( Int, index: Int, length: Int ) [function, hook(INT.signExtendBitRange)]

  syntax Bool ::= Int "<=Int" Int         [function, functional, klabel(_<=Int_), symbol, left, smt-hook(<=), latex({#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}), hook(INT.le)]
                | Int "<Int" Int          [function, functional, klabel(_<Int_), symbol, left, smt-hook(<), latex({#1}\mathrel{<_{\scriptstyle\it Int}}{#2}), hook(INT.lt)]
                | Int ">=Int" Int         [function, functional, klabel(_>=Int_), symbol, left, smt-hook(>=), latex({#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}), hook(INT.ge)]
                | Int ">Int" Int          [function, functional, klabel(_>Int_), symbol, left, smt-hook(>), latex({#1}\mathrel{>_{\scriptstyle\it Int}}{#2}), hook(INT.gt)]
                | Int "==Int" Int         [function, functional, klabel(_==Int_), symbol, left, smt-hook(=), latex({#1}\mathrel{{=}{=}_{\scriptstyle\it Int}}{#2}), hook(INT.eq)]
                | Int "=/=Int" Int        [function, functional, klabel(_=/=Int_), symbol, left, smt-hook(distinct), latex({#1}\mathrel{{=}{/}{=}_{\scriptstyle\it Int}}{#2}), hook(INT.ne)]
                | Int "dividesInt" Int    [function]
endmodule

module INT-SYMBOLIC [symbolic, kore]
  imports INT-COMMON
  imports ML-SYNTAX

  // Definability Conditions
  rule #Ceil(@I1:Int /Int   @I2:Int) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [anywhere, simplification]
  rule #Ceil(@I1:Int %Int   @I2:Int) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [anywhere, simplification]
  rule #Ceil(@I1:Int modInt @I2:Int) => {(@I2 =/=Int 0) #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [anywhere, simplification]
  rule #Ceil(@I1:Int >>Int  @I2:Int) => {(@I2 >=Int 0)  #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [anywhere, simplification]
  rule #Ceil(@I1:Int <<Int  @I2:Int) => {(@I2 >=Int 0)  #Equals true} #And #Ceil(@I1) #And #Ceil(@I2) [anywhere, simplification]

  // Arithmetic Normalization
  rule I +Int 0 => I [simplification]
  rule I -Int 0 => I [simplification]

  rule I +Int B => B +Int I          [concrete(I), symbolic(B), priority(51), simplification]
  rule A -Int I => A +Int (0 -Int I) [concrete(I), symbolic(A), priority(51), simplification]

  rule (A +Int I2) +Int I3 => A +Int (I2 +Int I3) [concrete(I2, I3), symbolic(A), simplification]
  rule I1 +Int (B +Int I3) => B +Int (I1 +Int I3) [concrete(I1, I3), symbolic(B), simplification]
  rule I1 -Int (B +Int I3) => (I1 -Int I3) -Int B [concrete(I1, I3), symbolic(B), simplification]
  rule I1 +Int (I2 +Int C) => (I1 +Int I2) +Int C [concrete(I1, I2), symbolic(C), simplification]
  rule I1 +Int (I2 -Int C) => (I1 +Int I2) -Int C [concrete(I1, I2), symbolic(C), simplification]
  rule (I1 -Int B) +Int I3 => (I1 +Int I3) -Int B [concrete(I1, I3), symbolic(B), simplification]
  rule I1 -Int (I2 +Int C) => (I1 -Int I2) -Int C [concrete(I1, I2), symbolic(C), simplification]
  rule I1 -Int (I2 -Int C) => (I1 -Int I2) +Int C [concrete(I1, I2), symbolic(C), simplification]
  rule (C -Int I2) -Int I3 => C -Int (I2 +Int I3) [concrete(I2, I3), symbolic(C), simplification]

  rule X modInt N => X requires 0 <=Int X andBool X <Int N [simplification]
  rule X   %Int N => X requires 0 <=Int X andBool X <Int N [simplification]

  rule I1 &Int (I2 &Int C) => (I1 &Int I2) &Int C [concrete(I1, I2), symbolic(C), simplification]

  // Bit-shifts
  rule X <<Int 0 => X [simplification]
  rule 0 <<Int _ => 0 [simplification]
  rule X >>Int 0 => X [simplification]
  rule 0 >>Int _ => 0 [simplification]
endmodule

module INT-KAST [kast]
  imports K-EQUAL
  imports INT-COMMON

  rule I1:Int ==Int I2:Int => I1 ==K I2

endmodule

module INT-KORE [kore]
  imports K-EQUAL
  imports INT-COMMON

  rule I1:Int ==K I2:Int => I1 ==Int I2

endmodule

module INT
  imports INT-COMMON
  imports INT-SYMBOLIC
  imports INT-KAST
  imports INT-KORE
  imports K-EQUAL

  rule bitRangeInt(I::Int, IDX::Int, LEN::Int) => (I >>Int IDX) modInt (1 <<Int LEN)

  rule signExtendBitRangeInt(I::Int, IDX::Int, LEN::Int) => (bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int 1))) modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))

  rule I1:Int divInt I2:Int => (I1 -Int (I1 modInt I2)) /Int I2
  requires I2 =/=Int 0
  rule
    I1:Int modInt I2:Int
  =>
    ((I1 %Int absInt(I2)) +Int absInt(I2)) %Int absInt(I2)
  requires I2 =/=Int 0    [concrete]

  rule minInt(I1:Int, I2:Int) => I1 requires I1 <=Int I2
  rule minInt(I1:Int, I2:Int) => I2 requires I1 >=Int I2

  rule I1:Int =/=Int I2:Int => notBool (I1 ==Int I2)
  rule (I1:Int dividesInt I2:Int) => (I2 %Int I1) ==Int 0

  syntax Int ::= freshInt(Int)    [freshGenerator, function, functional]
  rule freshInt(I:Int) => I

  syntax Int ::= randInt(Int) [function, hook(INT.rand)]
  syntax K ::= srandInt(Int) [function, hook(INT.srand)]
endmodule

module FLOAT-SYNTAX
  syntax Float [hook(FLOAT.Float)]
  syntax Float ::= r"([\\+-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+-]?([0-9]+(\\.[0-9]*)?|\\.[0-9]d+))?([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(1)]
  syntax Float ::= r"[\\+-]?Infinity([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(3)]
  syntax Float ::= r"NaN([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(3)]
endmodule

module FLOAT
  imports FLOAT-SYNTAX
  imports BOOL
  imports INT-SYNTAX


// For floating point SMT hooks: http://smtlib.cs.uiowa.edu/theories-FloatingPoint.shtml

  syntax Int ::= precisionFloat(Float) [function, functional, hook(FLOAT.precision)]
               | exponentFloat(Float) [function, functional, hook(FLOAT.exponent)]
               | exponentBitsFloat(Float) [function, functional, hook(FLOAT.exponentBits)]

  syntax Bool ::= signFloat(Float)      [function, functional, hook(FLOAT.sign)]
                | isNaN(Float)          [function, functional, smt-hook(fp.isNaN), hook(FLOAT.isNaN)]
                | isInfinite(Float)     [function, functional]

  syntax Float ::= "--Float" Float             [function, functional, smt-hook(fp.neg), hook(FLOAT.neg)]
                 > Float "^Float" Float        [function, left, latex({#1}^{#2}), hook(FLOAT.pow)]
                 > left:
                   Float "*Float" Float        [function, left, smt-hook((fp.mul roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}), hook(FLOAT.mul)]
                 | Float "/Float" Float        [function, left, smt-hook((fp.div roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}), hook(FLOAT.div)]
                 | Float "%Float" Float        [function, left, smt-hook((fp.rem roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}), hook(FLOAT.rem)]
                 > left:
                   Float "+Float" Float        [function, left, smt-hook((fp.add roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{+_{\scriptstyle\it Float}}{#2}), hook(FLOAT.add)]
                 | Float "-Float" Float        [function, left, smt-hook((fp.sub roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{-_{\scriptstyle\it Float}}{#2}), hook(FLOAT.sub)]

  syntax Float ::= rootFloat(Float, Int)        [function, hook(FLOAT.root)]
                 | absFloat(Float)              [function, functional, smt-hook(fp.abs), hook(FLOAT.abs)]
                 | roundFloat(Float, precision: Int, exponentBits: Int)  [function, hook(FLOAT.round)]
                 | floorFloat(Float)            [function, functional, hook(FLOAT.floor)]
                 | ceilFloat(Float)             [function, functional, hook(FLOAT.ceil)]
                 | expFloat(Float)              [function, functional, hook(FLOAT.exp)]
                 | logFloat(Float)              [function, hook(FLOAT.log)]
                 | sinFloat(Float)              [function, functional, hook(FLOAT.sin)]
                 | cosFloat(Float)              [function, functional, hook(FLOAT.cos)]
                 | tanFloat(Float)              [function, hook(FLOAT.tan)]
                 | asinFloat(Float)             [function, hook(FLOAT.asin)]
                 | acosFloat(Float)             [function, hook(FLOAT.acos)]
                 | atanFloat(Float)             [function, functional, hook(FLOAT.atan)]
                 | atan2Float(Float, Float)     [function, hook(FLOAT.atan2)]
                 | maxFloat(Float, Float)       [function, smt-hook(fp.max), hook(FLOAT.max)]
                 | minFloat(Float, Float)       [function, smt-hook(fp.min), hook(FLOAT.min)]
                 | sqrtFloat(Float)             [function]
                 | maxValueFloat(precision: Int, exponentBits: Int)      [function, hook(FLOAT.maxValue)]
                 | minValueFloat(precision: Int, exponentBits: Int)      [function, hook(FLOAT.minValue)]

  syntax Bool ::= Float "<=Float" Float       [function, left, smt-hook(fp.leq), latex({#1}\mathrel{\leq_{\scriptstyle\it Float}}{#2}), hook(FLOAT.le)]
                | Float "<Float" Float        [function, left, smt-hook(fp.lt), latex({#1}\mathrel{<_{\scriptstyle\it Float}}{#2}), hook(FLOAT.lt)]
                | Float ">=Float" Float       [function, left, smt-hook(fp.geq), latex({#1}\mathrel{\geq_{\scriptstyle\it Float}}{#2}), hook(FLOAT.ge)]
                | Float ">Float" Float        [function, left, smt-hook(fg.gt), latex({#1}\mathrel{>_{\scriptstyle\it Float}}{#2}), hook(FLOAT.gt)]
                | Float "==Float" Float       [function, left, smt-hook(fp.eq), latex({#1}\mathrel{==_{\scriptstyle\it Float}}{#2}), hook(FLOAT.eq), klabel(_==Float_)]
                | Float "=/=Float" Float      [function, left, smt-hook((not (fp.eq #1 #2))), latex({#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2})]


  rule F1:Float =/=Float F2:Float => notBool (F1 ==Float F2)

  syntax Float ::= Int2Float(Int, precision: Int, exponentBits: Int)    [function, latex({\\it{}Int2Float}), hook(FLOAT.int2float)]
  syntax Int ::= Float2Int(Float)    [function, functional, latex({\\it{}Float2Int}), hook(FLOAT.float2int)]

  rule sqrtFloat(F:Float) => rootFloat(F, 2)

  rule isInfinite(F:Float) => F >Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F)) orBool F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))

endmodule

module STRING-SYNTAX
  // Double Quoted Strings are of the form:
  // DoubleQuote StringChar* DoubleQuote
  // StringChar ::= ~[\"\n\r\\] // anything except for Newline, DoubleQuote and Backslash
  //              | [\\][nrtf\"\\] // Backslash followed by either 'nrtf', DoubleQuote or Backslash
  //              | [\\][x] 2*Hex // "\xFF"       Backslash 'x' followed by two   hexadecimal characters
  //              | [\\][u] 4*Hex // "\uFFFF"     Backslash 'u' followed by four  hexadecimal characters
  //              | [\\][U] 8*Hex // "\UFFffFFff" Backslash 'U' followed by eight hexadecimal characters
  //                              // the code must not be in the range [0xdfff, 0xd800] or exceed 0x10ffff
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\\n\\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"      [token]
endmodule

module STRING-COMMON
  imports STRING-SYNTAX
  imports INT
  imports FLOAT-SYNTAX
  imports K-EQUAL

  syntax String ::= String "+String" String    [function, functional, left, latex({#1}+_{\scriptstyle\it String}{#2}), hook(STRING.concat)]

  syntax Bool ::= String "==String" String [function, functional, left, hook(STRING.eq)]

  syntax Int ::= lengthString ( String ) [function, functional, hook(STRING.length)]
  syntax String ::= chrChar ( Int )      [function, hook(STRING.chr)]
  syntax Int ::= ordChar ( String )      [function, hook(STRING.ord)]

  syntax String ::= substrString ( String , startIndex: Int , endIndex: Int ) [function, functional, hook(STRING.substr)]
  syntax Int ::= findString ( haystack: String , needle: String , index: Int )   [function, hook(STRING.find)]
  syntax Int ::= rfindString ( haystack: String , needle: String , index: Int )  [function, hook(STRING.rfind)]
  syntax Int ::= findChar ( haystack: String , needles: String , index: Int )     [function, hook(STRING.findChar)]
  syntax Int ::= rfindChar ( haystack: String , needles: String , index: Int )    [function, hook(STRING.rfindChar)]

  syntax String ::= Float2String ( Float )              [function, functional, hook(STRING.float2string)]
  syntax String ::= Float2String ( Float , format: String )     [function, klabel(FloatFormat), hook(STRING.floatFormat)]
  syntax Float  ::= String2Float ( String )             [function, hook(STRING.string2float)]
  syntax Int    ::= String2Int   ( String )             [function, hook(STRING.string2int)]
  syntax String ::= Int2String   ( Int )                [function, functional, hook(STRING.int2string)]
  syntax String ::= Base2String  ( Int , base: Int )          [function, hook(STRING.base2string)]
  syntax Int    ::= String2Base  ( String , base: Int )       [function, hook(STRING.string2base)]


  syntax String ::= "replaceAll" "(" haystack: String "," needle: String "," replacement: String ")"      [function, functional, hook(STRING.replaceAll)]
  syntax String ::= "replace" "(" haystack: String "," needle: String "," replacement: String "," times: Int ")" [function, hook(STRING.replace)]
  syntax String ::= "replaceFirst" "(" haystack: String "," needle: String "," replacement: String ")"    [function, functional, hook(STRING.replaceFirst)]
  syntax Int ::= "countAllOccurrences" "(" haystack: String "," needle: String ")"            [function, functional, hook(STRING.countAllOccurrences)]

  syntax Bool ::= String "=/=String" String      [function, functional, left, hook(STRING.ne)]
  rule S1:String =/=String S2:String => notBool (S1 ==String S2)

  syntax Bool ::= String  "<String" String [function, functional, hook(STRING.lt)]
                | String "<=String" String [function, functional, hook(STRING.le)]
                | String  ">String" String [function, functional, hook(STRING.gt)]
                | String ">=String" String [function, functional, hook(STRING.ge)]

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

module STRING-KAST [kast]
  imports K-EQUAL
  imports STRING-COMMON

  rule S1:String ==String S2:String => S1 ==K S2

endmodule

module STRING-KORE [kore]
  imports K-EQUAL
  imports STRING-COMMON

  rule S1:String ==K S2:String => S1 ==String S2

endmodule

module STRING
  imports STRING-COMMON
  imports STRING-KAST
  imports STRING-KORE
endmodule

module STRING-BUFFER-IN-K [symbolic]
  imports BASIC-K
  imports STRING

  syntax StringBuffer ::= ".StringBuffer" [function, functional]
  syntax StringBuffer ::= StringBuffer "+String" String [function, functional, left, avoid]
  syntax StringBuffer ::= String
  syntax String ::= StringBuffer2String ( StringBuffer ) [function, functional]

  rule {SB:String +String S:String}<:StringBuffer => (SB +String S)::String
  rule .StringBuffer => ""
  rule StringBuffer2String(S:String) => S
endmodule

module STRING-BUFFER-HOOKED [concrete]
  imports BASIC-K
  imports STRING

  syntax StringBuffer [hook(BUFFER.StringBuffer)]
  syntax StringBuffer ::= ".StringBuffer" [function, functional, hook(BUFFER.empty), impure]
  syntax StringBuffer ::= StringBuffer "+String" String [function, functional, left, hook(BUFFER.concat), avoid]
  syntax String ::= StringBuffer2String ( StringBuffer ) [function, functional, hook(BUFFER.toString)]
endmodule

module STRING-BUFFER
  imports STRING-BUFFER-HOOKED
  imports STRING-BUFFER-IN-K
endmodule

module BYTES-HOOKED
  imports STRING-SYNTAX

  syntax Bytes [hook(BYTES.Bytes), token]

  syntax Bytes ::= ".Bytes" [function, functional, hook(BYTES.empty)]
  syntax Endianness ::= "LE" [klabel(littleEndianBytes), symbol]
                      | "BE" [klabel(bigEndianBytes), symbol]
  syntax Signedness ::= "Signed" [klabel(signedBytes), symbol]
                      | "Unsigned" [klabel(unsignedBytes), symbol]
  syntax Int ::= Bytes2Int(Bytes, Endianness, Signedness) [function, functional, hook(BYTES.bytes2int)]
  syntax Bytes ::= Int2Bytes(length: Int, Int, Endianness) [function, functional, hook(BYTES.int2bytes)]
                 | Int2Bytes(Int, Endianness, Signedness) [function, functional, klabel(Int2BytesNoLen)]
  syntax String ::= Bytes2String(Bytes) [function, functional, hook(BYTES.bytes2string)]
  syntax Bytes ::= String2Bytes(String) [function, functional, hook(BYTES.string2bytes)]

  syntax Bytes ::= Bytes "[" index: Int "<-" value: Int "]" [function, hook(BYTES.update)]
  syntax Int ::= Bytes "[" Int "]" [function, hook(BYTES.get)]
  syntax Bytes ::= substrBytes(Bytes, startIndex: Int, endIndex: Int) [function, hook(BYTES.substr)]
  syntax Bytes ::= replaceAtBytes(dest: Bytes, index: Int, src: Bytes) [function, hook(BYTES.replaceAt)]
  syntax Bytes ::= padRightBytes(Bytes, length: Int, value: Int) [function, hook(BYTES.padRight)]
                 | padLeftBytes(Bytes, length: Int, value: Int) [function, hook(BYTES.padLeft)]
  syntax Bytes ::= reverseBytes(Bytes) [function, functional, hook(BYTES.reverse)]

  syntax Int ::= lengthBytes(Bytes) [function, functional, hook(BYTES.length), smtlib(lengthBytes)]

  syntax Bytes ::= Bytes "+Bytes" Bytes [function, functional, hook(BYTES.concat), right]

  rule .Bytes => String2Bytes("")
endmodule

module BYTES-IN-K [symbolic, kast]
  imports INT
  imports K-EQUAL
  imports STRING
  imports STRING-BUFFER

  syntax Bytes ::= "nilBytes"
                 | Int ":" Bytes
  syntax Endianness ::= "LE" [klabel(littleEndianBytes), symbol]
                      | "BE" [klabel(bigEndianBytes), symbol]
  syntax Signedness ::= "Signed" [klabel(signedBytes), symbol]
                      | "Unsigned" [klabel(unsignedBytes), symbol]

  syntax Bytes ::= ".Bytes" [function, functional]
  rule .Bytes => nilBytes

  syntax Int ::= Bytes2Int(Bytes, Endianness, Signedness) [function, functional]
  rule Bytes2Int(nilBytes, _, _) => 0
  rule Bytes2Int(B : nilBytes, BE, Unsigned) => B
  rule Bytes2Int(B0 : B1 : BS, BE, Unsigned) => Bytes2Int(((B0 <<Int 8) |Int B1) : BS, BE, Unsigned)
  rule Bytes2Int(B0 : BS, BE, Signed) => signExtendBitRangeInt(Bytes2Int(B0 : BS, BE, Unsigned), 0, lengthBytes(B0 : BS) <<Int 3)
  rule Bytes2Int(B0 : BS, LE, S) => Bytes2Int(reverseBytes(B0 : BS), BE, S)

  syntax Bytes ::= Int2Bytes(Int, Bytes) [function, klabel(Int2BytesAux)]
  syntax Bytes ::= Int2Bytes(Int, Int, Endianness) [function, functional]
                 | Int2Bytes(Int, Endianness, Signedness) [function, functional, klabel(Int2BytesNoLen)]
  rule Int2Bytes(LEN, I, BE) => padLeftBytes(Int2Bytes(bitRangeInt(I, 0, LEN <<Int 3), nilBytes), LEN, #if I <Int 0 #then 255 #else 0 #fi)
  rule Int2Bytes(LEN, I, LE) => reverseBytes(Int2Bytes(LEN, I, BE))
  rule Int2Bytes(0, BS) => BS
  rule Int2Bytes(I, BS) => Int2Bytes(I >>Int 8, I &Int 255 : BS) requires I =/=Int 0

  syntax String ::= Bytes2String(Bytes, StringBuffer) [function, klabel(Bytes2StringAux)]
  syntax String ::= Bytes2String(Bytes) [function, functional]
  rule Bytes2String(BS) => Bytes2String(BS, .StringBuffer)
  rule Bytes2String(nilBytes, BUFFER) => StringBuffer2String(BUFFER)
  rule Bytes2String(B : BS, BUFFER) => Bytes2String(BS, BUFFER +String chrChar(B))

  syntax Bytes ::= String2Bytes(String) [function, functional]
  rule String2Bytes(S) => ordChar(substrString(S, 0, 1)) : String2Bytes(substrString(S, 1, lengthString(S))) requires lengthString(S) >=Int 1
  rule String2Bytes("") => nilBytes

  syntax Bytes ::= Bytes "[" Int "<-" Int "]" [function]
  rule BS [ N <- M ] => substrBytes(BS, 0, N) +Bytes M : substrBytes(BS, N +Int 1, lengthBytes(BS))

  syntax Int ::= Bytes "[" Int "]" [function]
  rule (B : _) [ 0 ] => B
  rule (_ : BS) [ I ] => BS [ I -Int 1] requires I >Int 0

  syntax Bytes ::= substrBytes(Bytes, Int, Int) [function]
  rule substrBytes(_, 0, 0) => nilBytes
  rule substrBytes(_ : BS, N, M) => substrBytes(BS, N -Int 1, M -Int 1) requires N >Int 0
  rule substrBytes(B : BS, 0, M) => B : substrBytes(BS, 0, M -Int 1) requires M >Int 0

  syntax Bytes ::= replaceAtBytes(Bytes, Int, Bytes) [function]
  rule replaceAtBytes(BS, _, nilBytes) => BS
  rule replaceAtBytes(B : BS, N, BS') => B : replaceAtBytes(BS, N -Int 1, BS') requires N >Int 0
  rule replaceAtBytes(_ : BS, 0, B : BS') => B : replaceAtBytes(BS, 0, BS')

  syntax Bytes ::= padRightBytes(Bytes, Int, Int) [function]
                 | padLeftBytes(Bytes, Int, Int) [function]
  rule padRightBytes(BS, LEN, VAL) => reverseBytes(padLeftBytes(reverseBytes(BS), LEN, VAL))
  rule padLeftBytes(BS, LEN, _) => BS requires lengthBytes(BS) >=Int LEN andBool 0 <=Int LEN
  rule padLeftBytes(BS, LEN, VAL) => padLeftBytes(VAL : BS, LEN, VAL) requires lengthBytes(BS) <Int LEN andBool 0 <=Int LEN

  syntax Bytes ::= reverseBytes(Bytes) [function, functional]
  syntax Bytes ::= reverseBytes(Bytes, Bytes) [function, klabel(reverseBytesAux)]
  rule reverseBytes(BS) => reverseBytes(BS, nilBytes)
  rule reverseBytes(nilBytes, BS) => BS
  rule reverseBytes(B : BS, BS') => reverseBytes(BS, B : BS')

  syntax Int ::= lengthBytes(Bytes) [function, functional, smtlib(lengthBytes)]
  syntax Int ::= lengthBytes(Bytes, Int) [function, klabel(lengthBytesAux), smtlib(lengthBytesAux)]
  rule lengthBytes(BS) => lengthBytes(BS, 0)
  rule lengthBytes(nilBytes, SIZE) => SIZE
  rule lengthBytes(_ : BS, SIZE) => lengthBytes(BS, SIZE +Int 1)

  syntax Bytes ::= Bytes "+Bytes" Bytes [function, functional, right]
  rule nilBytes +Bytes B2 => B2
  rule (B : BS) +Bytes B2 => B : (BS +Bytes B2)
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
  imports INT

  rule #Ceil(padRightBytes(_, LEN, VAL)) => {(0 <=Int LEN andBool 0 <=Int VAL andBool VAL <Int 256) #Equals true} [anywhere, simplification]
  rule #Ceil(padLeftBytes(_, LEN, VAL))  => {(0 <=Int LEN andBool 0 <=Int VAL andBool VAL <Int 256) #Equals true} [anywhere, simplification]
endmodule

module BYTES
  imports BYTES-CONCRETE
  imports BYTES-KORE
  imports BYTES-IN-K
  imports INT

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
  imports STRING

  syntax String ::= Id2String ( Id )    [function, functional, hook(STRING.token2string)]
  syntax Id ::= String2Id (String) [function, functional, hook(STRING.string2token)]
  syntax Id ::= freshId(Int)    [freshGenerator, function, functional]
endmodule

module ID
  imports ID-COMMON
  imports ID-SYMBOLIC

  rule freshId(I:Int) => String2Id("_" +String Int2String(I))
endmodule

module ID-SYMBOLIC [symbolic, kast]
  imports ID-COMMON
  imports STRING

  syntax KItem  ::= "#parseIdToken"  "(" String "," String ")"  [function, hook(STRING.parseToken)]
  rule String2Id(S:String) => {#parseIdToken("Id", S)}:>Id
endmodule

module K-EQUAL-SYNTAX
  imports BOOL
  imports BASIC-K

  syntax Bool ::= left:
                  K "==K" K           [function, functional, smt-hook(=), hook(KEQUAL.eq), klabel(_==K_), symbol, latex({#1}\mathrel{=_K}{#2}), equalEqualK]
                | K "=/=K" K          [function, functional, smt-hook(distinct), hook(KEQUAL.ne), klabel(_=/=K_), symbol, latex({#1}\mathrel{\neq_K}{#2}), notEqualEqualK]

  syntax priorities equalEqualK notEqualEqualK > boolOperation mlOp

  syntax {Sort} Sort ::= "#if" Bool "#then" Sort "#else" Sort "#fi"   [function, functional, smt-hook(ite), hook(KEQUAL.ite)]

endmodule

module K-EQUAL-KORE [kore]
  import BOOL
  import K-EQUAL-SYNTAX

  rule K1:Bool ==K K2:Bool => K1 ==Bool K2

endmodule

module K-EQUAL-KAST [kast]
  import BOOL
  import K-EQUAL-SYNTAX

  rule K1:Bool ==Bool K2:Bool => K1 ==K K2

endmodule

module K-EQUAL
  import BOOL
  import K-EQUAL-SYNTAX
  import K-EQUAL-KAST
  import K-EQUAL-KORE

  rule K1:K =/=K K2:K => notBool (K1 ==K K2)

  rule #if C:Bool #then B1::K #else _ #fi => B1 requires C
  rule #if C:Bool #then _ #else B2::K #fi => B2 requires notBool C

endmodule

module K-REFLECTION
  imports BASIC-K
  imports STRING
  imports K-REFLECTION-SYMBOLIC

  syntax K ::= "#configuration" [function, impure, hook(KREFLECTION.configuration)]
  syntax String ::= #sort(K) [function, hook(KREFLECTION.sort)]
  syntax KItem ::= #fresh(String)   [function, hook(KREFLECTION.fresh), impure]
  syntax KItem ::= getKLabel(K)  [function, hook(KREFLECTION.getKLabel)]

  syntax String ::= #getenv(String) [function, impure, hook(KREFLECTION.getenv)]

  // meaningful only for the purposes of compilation to a binary, otherwise
  // undefined
  syntax List ::= #argv() [function, hook(KREFLECTION.argv)]

  // Takes as input a string and returns a K term
  syntax {Sort} Sort ::= #parseKORE(String) [function, hook(KREFLECTION.parseKORE)]
  syntax {Sort} Sort ::= #parseKAST(String) [function, hook(KREFLECTION.parseKAST)]
  syntax IOError ::= "#noParse" "(" String ")" [klabel(#noParse), symbol]

endmodule

module K-REFLECTION-SYMBOLIC [symbolic]
  imports BASIC-K
  imports STRING

  // return empty string if the term has no klabel
  syntax String ::= #getKLabelString(K) [function, hook(KREFLECTION.getKLabelString)]

  // return true if no variable nor unresolved function appears in any subterm
  syntax Bool ::= #isConcrete(K) [function, hook(KREFLECTION.isConcrete)]
  syntax Bool ::= #isVariable(K) [function, hook(KREFLECTION.isVariable)]
endmodule

module K-IO
  imports LIST
  imports STRING

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
               | "#tell" "(" fd: Int ")" [function, hook(IO.tell), impure]
               | "#getc" "(" fd: Int ")"             [function, hook(IO.getc), impure]
               | "#accept" "(" fd: Int ")" [function, hook(IO.accept), impure]
  syntax IOString ::= "#read" "(" fd: Int "," length: Int ")"    [function, hook(IO.read), impure]

  syntax K ::= "#close" "(" fd: Int ")" [function, hook(IO.close), impure]
             | "#seek" "(" fd: Int "," index: Int ")" [function, hook(IO.seek), impure]
             | "#seekEnd" "(" fd: Int "," fromEnd: Int ")" [function, hook(IO.seekEnd), impure]
             | "#putc" "(" fd: Int "," value: Int ")"      [function, hook(IO.putc), impure]
             | "#write" "(" fd: Int "," value: String ")" [function, hook(IO.write), impure]
             | "#lock" "(" fd: Int "," endIndex: Int ")" [function, hook(IO.lock), impure]
             | "#unlock" "(" fd: Int "," endIndex: Int ")" [function, hook(IO.unlock), impure]
             | "#shutdownWrite" "(" fd: Int ")" [function, hook(IO.shutdownWrite), impure]

  syntax KItem ::= "#stat" "(" String ")" [function, hook(IO.stat), impure]
                 | "#lstat" "(" String ")" [function, hook(IO.lstat), impure]
                 | "#opendir" "(" String ")" [function, hook(IO.opendir), impure]

  syntax Int ::= "#time" "(" ")" [function, hook(IO.time), impure]

  rule #open(S:String) => #open(S:String, "r+")

  syntax Int ::= "#stdin"   [function, functional]
                | "#stdout" [function, functional]
                | "#stderr" [function, functional]

  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

  syntax Stream ::= #buffer(K)

// ------------------------------
// System

  // executes the given command line with `sh -c cmd:String`
  syntax KItem ::= #system ( String ) [function, hook(IO.system), impure]
                 | "#systemResult" "(" Int /* exit code */ "," String /* stdout */ "," String /* stderr */ ")" [klabel(#systemResult), symbol]

  syntax K ::= #logToFile(name: String, value: String) [function, functional, hook(IO.log), impure, returnsUnit, symbol]
  // creates a temporary file in the default system location
  syntax IOFile ::= #mkstemp(template: String) [function, hook(IO.mkstemp), impure]
  syntax IOFile ::= IOError
                  | "#tempFile" "(" path: String "," fd: Int ")" [klabel(#tempFile), symbol]
  // Remove a file or empty directory from the disk. Returns .K on success or an IOError on failure.
  syntax K ::= #remove(path: String) [function, functional, hook(IO.remove), impure]
endmodule

// NOTE: DO NOT DIRECTLY IMPORT *-STREAM MODULES
// These stream modules will be automatically instantiated and implicitly imported
// into the main module when `stream` attributes appear in configuration cells.
// Only `Stream` productions and `[stream]` rules will be imported.
// The cell name will be replaced with the one of the main configuration.

module STDIN-STREAM
  imports K-IO
  imports K-REFLECTION

  syntax Stream ::= #istream(Int)
  syntax Stream ::= #parseInput(String, String)

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

  rule [stdinParseArbitrarySort]:
       <stdin>
       (ListItem(#parseInput(Sort:String, Delimiters:String))
       => ListItem(#parseKAST(substrString(S, 0, findChar(S, Delimiters, 0)))))
       ListItem(#buffer(S:String => substrString(S,findChar(S, Delimiters, 0) +Int 1, lengthString(S))))
       _:List
       </stdin>
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool Sort ==String "K"
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

  syntax Stream ::= #ostream(Int)

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
  imports INT

  /*@ Function returning the bit width of this machine integer. */
  syntax {Width} Int ::= bitwidthMInt(MInt{Width})   [function, functional, hook(MINT.bitwidth)]

  /*@
   * Functions returning the signed and unsigned interpretations of this
   * machine integers.
   *   svalue  returns an integer between -2^(bitwidth - 1) and
   *           2^(bitwidth - 1) - 1
   *   uvalue  returns an integer between 0 and 2^bitwidth - 1
   */
  syntax {Width} Int ::= MInt2Signed(MInt{Width})     [function, functional, hook(MINT.svalue)]
                       | MInt2Unsigned(MInt{Width})     [function, functional, hook(MINT.uvalue), smt-hook(bv2int)]

  syntax {Width} MInt{Width} ::= Int2MInt(Int) [function, functional, hook(MINT.integer), smt-hook(int2bv)]

  /*@
   * Functions for signed and unsigned minimum and maximum values of a machine
   * integer on a given bit width.
   */
  syntax Int ::= sminMInt(Int)    [function]
               | smaxMInt(Int)    [function]
               | uminMInt(Int)    [function]
               | umaxMInt(Int)    [function]
  rule sminMInt(N:Int) => 0 -Int (1 <<Int (N -Int 1))
  rule smaxMInt(N:Int) => (1 <<Int (N -Int 1)) -Int 1
  rule uminMInt(_:Int) => 0
  rule umaxMInt(N:Int) => (1 <<Int N) -Int 1

  /*@
   * Functions checking whether a given integer can be represented on as signed
   * or unsigned on a given bit width without overflow.
   */
  syntax Bool ::= soverflowMInt(Int, Int)   [function]
                | uoverflowMInt(Int, Int)   [function]
  rule
    soverflowMInt(N:Int, I:Int)
  =>
    I <Int sminMInt(N) orBool I >Int smaxMInt(N)
  rule
    uoverflowMInt(N:Int, I:Int)
  =>
    I <Int uminMInt(N) orBool I >Int umaxMInt(N)

  syntax {Width} MInt{Width} ::= "~MInt" MInt{Width} [function, functional, hook(MINT.not), smt-hook(bvnot)]

                               | "--MInt" MInt{Width} [function, functional, hook(MINT.neg), smt-hook(bvuminus)]
  /*@
   * Multiplication, division and reminder
   * mul        operation is the same for signed and unsigned integers in twos complement
   * sdiv/srem  operation interprets operands as signed; undefined if the second
   *            argument is 0
   * udiv/urem  operation interprets operands as unsigned; undefined if the
   *            second argument is 0
   */
                               > left:
                                 MInt{Width} "*MInt" MInt{Width} [function, functional, hook(MINT.mul), smt-hook(bvmul)]
                               | MInt{Width} "/sMInt" MInt{Width} [function, hook(MINT.sdiv), smt-hook(bvsdiv)]
                               | MInt{Width} "%sMInt" MInt{Width} [function, hook(MINT.srem), smt-hook(bvsrem)]
                               | MInt{Width} "/uMInt" MInt{Width} [function, hook(MINT.udiv), smt-hook(bvudiv)]
                               | MInt{Width} "%uMInt" MInt{Width} [function, hook(MINT.urem), smt-hook(bvurem)]

  /*@
   * Addition and subtraction
   * add        operation is the same for signed and unsigned integers in twos complement
   * sub        operation is the same for signed and unsigned integers in twos complement
   */
                               > left:
                                 MInt{Width} "+MInt" MInt{Width} [function, functional, hook(MINT.add), smt-hook(bvadd)]
                               | MInt{Width} "-MInt" MInt{Width} [function, functional, hook(MINT.sub), smt-hook(bvsub)]


  /*@
   * Shift operations; the second operand must be non-negative
   *
   * shl        operation is the same for arithmetic and logic shift
   * ashr       arithmetic shift: filling with leftmost bit (sign extension)
   * lshr       logical shift: filling with zeros
   */
                               > left:
                                 MInt{Width} "<<MInt" MInt{Width} [function, hook(MINT.shl), smt-hook(bvshl)]
                               | MInt{Width} ">>aMInt" MInt{Width} [function, hook(MINT.ashr), smt-hook(bvashr)]
                               | MInt{Width} ">>lMInt" MInt{Width} [function, hook(MINT.lshr), smt-hook(bvlshr)]

  /*@
   * Bitwise operations
   */
                               > left:
                                 MInt{Width} "&MInt" MInt{Width} [function, functional, hook(MINT.and), smt-hook(bvand)]
                               > left:
                                 MInt{Width} "xorMInt" MInt{Width} [function, functional, hook(MINT.xor), smt-hook(bvxor)]
                               > left:
                                 MInt{Width} "|MInt" MInt{Width} [function, functional, hook(MINT.or), smt-hook(bvor)]

  /*@ Comparison operations */
  syntax {Width} Bool ::= MInt{Width} "<sMInt" MInt{Width} [function, functional, hook(MINT.slt), smt-hook(bvslt)]
                        | MInt{Width} "<uMInt" MInt{Width} [function, functional, hook(MINT.ult), smt-hook(bvult)]
                        | MInt{Width} "<=sMInt" MInt{Width} [function, functional, hook(MINT.sle), smt-hook(bvsle)]
                        | MInt{Width} "<=uMInt" MInt{Width} [function, functional, hook(MINT.ule), smt-hook(bvule)]
                        | MInt{Width} ">sMInt" MInt{Width} [function, functional, hook(MINT.sgt), smt-hook(bvsgt)]
                        | MInt{Width} ">uMInt" MInt{Width} [function, functional, hook(MINT.ugt), smt-hook(bvugt)]
                        | MInt{Width} ">=sMInt" MInt{Width} [function, functional, hook(MINT.sge), smt-hook(bvsge)]
                        | MInt{Width} ">=uMInt" MInt{Width} [function, functional, hook(MINT.uge), smt-hook(bvuge)]
                        | MInt{Width} "==MInt" MInt{Width} [function, functional, hook(MINT.eq), smt-hook(=)]
                        | MInt{Width} "=/=MInt" MInt{Width} [function, functional, hook(MINT.ne), smt-hook(distinct)]

  syntax {Width} MInt{Width} ::= sMaxMInt(MInt{Width}, MInt{Width}) [function, functional, hook(MINT.smax), smt-hook((ite (bvslt #1 #2) #2 #1))]
                               | sMinMInt(MInt{Width}, MInt{Width}) [function, functional, hook(MINT.smin), smt-hook((ite (bvslt #1 #2) #1 #2))]
                               | uMaxMInt(MInt{Width}, MInt{Width}) [function, functional, hook(MINT.umax), smt-hook((ite (bvult #1 #2) #2 #1))]
                               | uMinMInt(MInt{Width}, MInt{Width}) [function, functional, hook(MINT.umin), smt-hook((ite (bvult #1 #2) #1 #2))]

  /*@
   * Returns a machine integer with either the same low-order bits and a larger width, or a truncated value and a smaller width.
   * Bits will be truncated starting from the most significant bit.
   */
  syntax {Width1, Width2} MInt{Width1} ::= roundMInt(MInt{Width2}) [function, functional, hook(MINT.round)]
endmodule

module CONFIGURATION-PRIMITIVES
    syntax K ::= "#RESTORE_CONFIGURATION" "(" K ")"  [klabel(#RESTORE_CONFIGURATION)]
endmodule

module STRATEGY
    imports ML-SYNTAX
    imports KVARIABLE-SYNTAX
    imports K-EQUAL

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
    imports syntax STRATEGY
    imports RULE-TAG-SYNTAX
    rule ~ regular => ^ regular [anywhere]
endmodule

module DEFAULT-STRATEGY-SYMBOLIC [symbolic]
    imports syntax STRATEGY
    imports RULE-TAG-SYNTAX
    rule <s> ~ regular => ^ regular ... </s>
endmodule

module DEFAULT-STRATEGY
    imports syntax STRATEGY
    imports DEFAULT-STRATEGY-CONCRETE
    imports DEFAULT-STRATEGY-SYMBOLIC

    rule initSCell(_) => <s> ^ regular </s>
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
    rule <s> #STUCK() ~> (S:Strategy => .) ... </s>
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
