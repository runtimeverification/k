// Copyright (c) 2015-2018 K Team. All Rights Reserved.
require "kast.k"

module DOMAINS-SYNTAX
  imports ID
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
  imports K-REFLECTION
endmodule

module ARRAY-SYNTAX
  imports LIST

  syntax Array [hook(ARRAY.Array), unit(arrayCtor), element(_[_<-_])]
  syntax Array ::= makeArray(Int, K) [function, hook(ARRAY.make), impure]

  syntax K ::= Array "[" Int "]" [function, hook(ARRAY.lookup)]
  syntax Array ::= Array "[" Int "<-" K "]" [function, hook(ARRAY.update), klabel(_[_<-_]), symbol]
  syntax Array ::= Array "[" Int "<-" "undef" "]" [function, hook(ARRAY.remove)]
  syntax Array ::= updateArray(Array, Int, List) [function, hook(ARRAY.updateAll)]
  /*@ Sets a range of indices (given by an index into the array and the number
   of indices to set) to the same value. */
  syntax Array ::= fillArray(Array, Int, Int, K) [function, hook(ARRAY.fill)]

  syntax Bool ::= Int "in_keys" "(" Array ")" [function, hook(ARRAY.in_keys)]
endmodule

module ARRAY-CONCRETE [concrete]
  imports ARRAY-SYNTAX
  imports LIST
  imports STRING-SYNTAX

  syntax Array ::= makeEmptyArray(Int) [function, hook(ARRAY.makeEmpty), impure]
                 | arrayCtor(String, Int) [function, hook(ARRAY.ctor), symbol]
endmodule

module ARRAY-SYMBOLIC [symbolic]
  imports ARRAY-SYNTAX
  imports MAP
  imports INT

  syntax Array ::= array(Map, Int, K)

  rule makeArray(Len:Int, K:K) => array(.Map, Len, K)

  rule array(_ I |-> K:K, _, _) [ I:Int ] => K
  rule array(M:Map, _, K:K) [ I:Int ] => K requires notBool I in_keys(M)

  rule array(M:Map, Len:Int, K:K) [ I:Int <- K2:K ] => array(M [ I <- K2 ], Len, K)
       requires I >=Int 0 andBool I <Int Len
  rule array(M:Map, Len:Int, K:K) [ I:Int <- _ ] => array(M, Len, K)
       requires I<Int 0 orBool I >=Int Len
  rule array(M:Map, Len:Int, K:K) [ I:Int <- undef ] => array(M [ I <- undef ], Len, K)

  rule updateArray(array(M:Map, Len:Int, K:K), _, .List) => array(M, Len, K)
  rule updateArray(array(M:Map, Len:Int, K:K), I:Int, ListItem(K2:K) L:List) => updateArray(array(M, Len, K) [ I <- K2 ], I +Int 1, L)

  rule fillArray(array(M:Map, Len:Int, K:K), _, 0, _) => array(M, Len, K)
  rule fillArray(array(M:Map, Len:Int, K:K), I:Int, N:Int, K2:K) => fillArray(array(M, Len, K) [ I <- K2 ], I +Int 1, N -Int 1, K2)
       requires N >Int 0

  rule I:Int in_keys(array(M:Map, _, _)) => I in_keys(M)
endmodule

module ARRAY
  imports ARRAY-CONCRETE
  imports ARRAY-SYMBOLIC
endmodule

module MAP
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
  syntax Map ::= ".Map"                         [function, hook(MAP.unit), klabel(.Map), symbol, latex(\dotCt{Map})]
               // breaks klabel uniqueness
               //| "."                            [function, hook(MAP.unit)]
  /*@ Construct a singleton Map (a Map with only one key/value pair). The key
   is on the left and the value is on the right */
  syntax Map ::= K "|->" K                      [function, hook(MAP.element), klabel(_|->_), symbol, latex({#1}\mapsto{#2})]

  syntax priorities _|->_ > _Map_ .Map
  syntax non-assoc _|->_

  /*@ Retrieve the value associated with the given key */
  syntax K ::= Map "[" K "]"                    [function, hook(MAP.lookup), klabel(Map:lookup), symbol]

  syntax K ::= Map "[" K "]" "orDefault" K      [function, hook(MAP.lookupOrDefault), klabel(Map:lookupOrDefault)]

  /*@ Update a Map in form of  of keys and values: */
  syntax Map ::= Map "[" K "<-" K "]"           [function, hook(MAP.update), prefer]

  /*@ Remove key/value pair associated with the key from map? */
  syntax Map ::= Map "[" K "<-" "undef" "]"     [function, hook(MAP.remove), klabel(_[_<-undef]), symbol]

  /*@ Get the difference of two maps interpreted as sets of entries
   ($M_1 \setminus M2$) */
  syntax Map ::= Map "-Map" Map                 [function, hook(MAP.difference), latex({#1}-_{\it Map}{#2})]

  /*@ Update the first map by adding all key/value pairs in the second map. If a
   key in the first map exists also in the second map, its associated value will
   be overwritten by the value from the second map. */
  syntax Map ::= updateMap(Map, Map)            [function, hook(MAP.updateAll)]

  /*@ Update the Map by removing all key/value pairs with the key in the Set. */
  syntax Map ::= removeAll(Map, Set)            [function, hook(MAP.removeAll)]

  /*@ Get a Set consisting of all keys in the Map:*/
  syntax Set ::= keys(Map)                      [function, hook(MAP.keys)]
  syntax List ::= "keys_list" "(" Map ")"       [function, hook(MAP.keys_list)]

  syntax Bool ::= K "in_keys" "(" Map ")"       [function, hook(MAP.in_keys)]

  /*@ Get a List consisting of all values in the Map: */
  syntax List ::= values(Map)                   [function, hook(MAP.values)]

  /*@ Get the Map size (number of key/value pairs) */
  syntax Int ::= size(Map)                      [function, hook(MAP.size), klabel(sizeMap)]

  /*@ Check map inclusion */
  syntax Bool ::= Map "<=Map" Map               [function, hook(MAP.inclusion)]

  /*@ Get an arbitrarily chosen key of the Map  */
  syntax K ::= choice(Map)                      [function, hook(MAP.choice), klabel(Map:choice)]
endmodule

module SET
  imports INT-SYNTAX
  imports BASIC-K

  syntax Set [hook(SET.Set)]

  /*@ \section{Description} The Set represents a mathematical set (a collection
   of unique items). */

  /*@ Construct a new Set as the union of two different sets ($A \cup B$) */
  syntax Set ::= Set Set                  [left, function, hook(SET.concat), klabel(_Set_), symbol, assoc, comm, unit(.Set), idem, element(SetItem), format(%1%n%2)]
  /*@ Construct an empty Set */
  syntax Set ::= ".Set"                   [function, hook(SET.unit), klabel(.Set), symbol, latex(\dotCt{Set})]
               //| "."
  /*@ Construct a singleton Set (a Set with only one element $\{ a \}$). To add
   an element $a$ to a set $A$, construct the union of the singleton set
   $\{ a \}$ and $A$ ($\{ a \} \cup A$). */
  syntax Set ::= SetItem(K)               [function, hook(SET.element), klabel(SetItem), symbol]

  /*@ Get the intersection of two sets ($A \cap B$) */
  syntax Set ::= intersectSet(Set, Set)   [function, hook(SET.intersection)]

  /*@ Get the difference of two sets ($A \setminus B$)*/
  syntax Set ::= Set "-Set" Set           [function, hook(SET.difference), latex({#1}-_{\it Set}{#2}), klabel(Set:difference), symbol]

  /*@ Check element membership in a set ($a \in A$) */
  syntax Bool ::= K "in" Set              [function, hook(SET.in), klabel(Set:in), symbol]

  /*@ Check set inclusion ($A \subseteq B$) */
  syntax Bool ::= Set "<=Set" Set         [function, hook(SET.inclusion)]

  /*@ Get the cardinality of a set ($|A|$) */
  syntax Int ::= size(Set)                [function, hook(SET.size)]

  /*@ Get an arbitrarily chosen element of the Set */
  syntax K ::= choice(Set)                [function, hook(SET.choice), klabel(Set:choice)]

  /* set difference axioms */
  // TODO(AndreiS): remove this if not used
  //rule S1:Set -Set (SetItem(K:K) S2:Set) => S1 -Set S2
  //requires notBool(K in S1)
  //rule S:Set -Set .Set => S
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
  syntax List ::= List List               [left, function, hook(LIST.concat), klabel(_List_), symbol, smtlib(smt_seq_concat), assoc, unit(.List), element(ListItem), format(%1%n%2)]
  /*@ Construct an empty List: */
  syntax List ::= ".List"                 [function, hook(LIST.unit), klabel(.List), symbol, smtlib(smt_seq_nil), latex(\dotCt{List})]
                //| "."
  /*@ Construct a singleton List (a list with only  one element) */
  syntax List ::= ListItem(K)             [function, hook(LIST.element), klabel(ListItem), symbol, smtlib(smt_seq_elem)]

  /*@ Get an element form the List by index. Positive indices mean from the
   beginning (0 is the first element), and negative indices mean from the end
   (-1 is the last element). */
  syntax K ::= List "[" Int "]"           [function, hook(LIST.get), klabel(List:get), symbol]

  /*@ Remove elements from the beginning and the end of the List. */
  syntax List ::= range(List, Int, Int)   [function, hook(LIST.range), klabel(List:range), symbol]

  /*@ Check element membership in the given list */
  syntax Bool ::= K "in" List             [function, hook(LIST.in), klabel(_inList_)]

  /*@ Get the list length */
  syntax Int ::= size(List)               [function, hook(LIST.size), klabel (sizeList), smtlib(smt_seq_len)]
endmodule

module COLLECTIONS
  imports LIST
  imports SET
  imports MAP

  syntax List ::= Set2List(Set) [function, hook(SET.set2list)]
  syntax Set ::= List2Set(List) [function, hook(SET.list2set)]

endmodule

module BOOL-SYNTAX
  syntax Bool [hook(BOOL.Bool)]
  syntax Bool ::= "true"  [token]
  syntax Bool ::= "false" [token]
endmodule

module BOOL
  imports BASIC-K
  imports BOOL-SYNTAX
  syntax Bool ::= "notBool" Bool          [function, klabel(notBool_), symbol, smtlib(not), boolOperation, latex(\neg_{\scriptstyle\it Bool}{#1}), hook(BOOL.not)]
                > Bool "andBool" Bool     [function, klabel(_andBool_), symbol, left, smtlib(and), boolOperation, latex({#1}\wedge_{\scriptstyle\it Bool}{#2}), hook(BOOL.and)]
                | Bool "andThenBool" Bool [function, left, smtlib(and), boolOperation, hook(BOOL.andThen)]
                | Bool "xorBool" Bool     [function, left, smtlib(xor), boolOperation, hook(BOOL.xor)]
                | Bool "orBool" Bool      [function, left, smtlib(or), boolOperation, latex({#1}\vee_{\scriptstyle\it Bool}{#2}), hook(BOOL.or)]
                | Bool "orElseBool" Bool  [function, left, smtlib(or), boolOperation, hook(BOOL.orElse)]
                | Bool "impliesBool" Bool [function, left, smtlib(=>), boolOperation, hook(BOOL.implies)]
                > left:
                  Bool "==Bool" Bool      [function, left, smtlib(=), hook(BOOL.eq)]
                | Bool "=/=Bool" Bool     [function, left, smtlib(distinct), hook(BOOL.ne)]

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
  rule B1:Bool xorBool B2:Bool => notBool (B1 ==Bool B2)

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

module INT
  imports INT-SYNTAX
  imports BOOL
  imports K-EQUAL

  syntax Int ::= "~Int" Int                     [function, latex(\mathop{\sim_{\scriptstyle\it Int}}{#1}), hook(INT.not)]
               > left:
                 Int "^Int" Int                 [function, left, smtlib(^), latex({#1}\mathrel{{\char`\^}_{\!\scriptstyle\it Int}}{#2}), hook(INT.pow)]
               | Int "^%Int" Int Int            [function, left, smtlib((mod (^ #1 #2) #3)), hook(INT.powmod)]
               > left:
                 Int "*Int" Int                 [function, left, smtlib(*), latex({#1}\mathrel{\ast_{\scriptstyle\it Int}}{#2}), hook(INT.mul)]
               /* FIXME: translate /Int and %Int into smtlib */
               /* /Int and %Int implement t-division */
               | Int "/Int" Int                 [function, left, smtlib(div), latex({#1}\mathrel{\div_{\scriptstyle\it Int}}{#2}), hook(INT.tdiv)]
               | Int "%Int" Int                 [function, left, smtlib(mod), latex({#1}\mathrel{\%_{\scriptstyle\it Int}}{#2}), hook(INT.tmod)]
               /* divInt and modInt implement e-division */
               | Int "divInt" Int               [function, left, smtlib(div), hook(INT.ediv)]
               | Int "modInt" Int               [function, left, smtlib(mod), hook(INT.emod)]
               > left:
                 Int "+Int" Int                 [function, left, smtlib(+), latex({#1}\mathrel{+_{\scriptstyle\it Int}}{#2}), hook(INT.add)]
               | Int "-Int" Int                 [function, left, smtlib(-), latex({#1}\mathrel{-_{\scriptstyle\it Int}}{#2}), hook(INT.sub)]
               > left:
                 Int ">>Int" Int                [function, left, latex({#1}\mathrel{\gg_{\scriptstyle\it Int}}{#2}), hook(INT.shr)]
               | Int "<<Int" Int                [function, left, latex({#1}\mathrel{\ll_{\scriptstyle\it Int}}{#2}), hook(INT.shl)]
               > left:
                 Int "&Int" Int                 [function, left, latex({#1}\mathrel{\&_{\scriptstyle\it Int}}{#2}), hook(INT.and)]
               > left:
                 Int "xorInt" Int               [function, left, latex({#1}\mathrel{\oplus_{\scriptstyle\it Int}}{#2}), hook(INT.xor)]
               > left:
                 Int "|Int" Int                 [function, left, latex({#1}\mathrel{|_{\scriptstyle\it Int}}{#2}), hook(INT.or)]
  syntax Int ::= "minInt" "(" Int "," Int ")"   [function, smtlib(int_min), hook(INT.min)]
               | "maxInt" "(" Int "," Int ")"   [function, smtlib(int_max), hook(INT.max)]
               | absInt ( Int )                 [function, smtlib(int_abs), hook(INT.abs)]
               | log2Int ( Int )                [function, hook(INT.log2)]

  syntax Int ::= bitRangeInt           ( Int, indexInt: Int, lengthInt: Int ) [function, hook(INT.bitRange)]
  syntax Int ::= signExtendBitRangeInt ( Int, indexInt: Int, lengthInt: Int ) [function, hook(INT.signExtendBitRange)]

  rule bitRangeInt(I, IDX, LEN) => (I >>Int IDX) modInt (1 <<Int LEN)

  rule signExtendBitRangeInt(I, IDX, LEN) => (bitRangeInt(I, IDX, LEN) +Int (1 <<Int (LEN -Int 1))) modInt (1 <<Int LEN) -Int (1 <<Int (LEN -Int 1))

  rule I1:Int divInt I2:Int => (I1 -Int (I1 modInt I2)) /Int I2
  requires I2 =/=Int 0
  rule
    I1:Int modInt I2:Int
  =>
    ((I1 %Int absInt(I2)) +Int absInt(I2)) %Int absInt(I2)
  requires I2 =/=Int 0    [concrete]

  rule minInt(I1:Int, I2:Int) => I1 requires I1 <=Int I2
  rule minInt(I1:Int, I2:Int) => I2 requires I1 >=Int I2

  syntax Bool ::= Int "<=Int" Int         [function, left, smtlib(<=), latex({#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}), hook(INT.le)]
                | Int "<Int" Int          [function, left, smtlib(<), latex({#1}\mathrel{<_{\scriptstyle\it Int}}{#2}), hook(INT.lt)]
                | Int ">=Int" Int         [function, left, smtlib(>=), latex({#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}), hook(INT.ge)]
                | Int ">Int" Int          [function, left, smtlib(>), latex({#1}\mathrel{>_{\scriptstyle\it Int}}{#2}), hook(INT.gt)]
                | Int "==Int" Int         [function, left, smtlib(=), latex({#1}\mathrel{{=}{=}_{\scriptstyle\it Int}}{#2}), hook(INT.eq), klabel(_==Int_)]
                | Int "=/=Int" Int        [function, left, smtlib(distinct), latex({#1}\mathrel{{=}{/}{=}_{\scriptstyle\it Int}}{#2}), hook(INT.ne)]
                | Int "dividesInt" Int    [function]

  rule I1:Int ==Int I2:Int => I1 ==K I2
  rule I1:Int =/=Int I2:Int => notBool (I1 ==Int I2)
  rule (I1:Int dividesInt I2:Int) => (I2 %Int I1) ==Int 0

  syntax Int ::= freshInt(Int)    [freshGenerator, function]
  rule freshInt(I:Int) => I

  syntax Int ::= randInt(Int) [function, hook(INT.rand)]
  syntax K ::= srandInt(Int) [function, hook(INT.srand)]
endmodule

module FLOAT-SYNTAX
  syntax Float [hook(FLOAT.Float)]
  syntax Float ::= r"([\\+-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+-]?([0-9]+(\\.[0-9]*)?|\\.[0-9]d+))?([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token, prec(1)]
  syntax Float ::= r"[\\+-]?Infinity([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token]
  syntax Float ::= r"NaN([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token]
endmodule

module FLOAT
  imports FLOAT-SYNTAX
  imports BOOL
  imports INT-SYNTAX

  syntax Int ::= precisionFloat(Float) [function, hook(FLOAT.precision)]
               | exponentFloat(Float) [function, hook(FLOAT.exponent)]
               | exponentBitsFloat(Float) [function, hook(FLOAT.exponentBits)]

  syntax Bool ::= signFloat(Float)      [function, hook(FLOAT.sign)]
                | isNaN(Float)          [function, smtlib((not (== #1 #1))), hook(FLOAT.isNaN)]
                | isInfinite(Float)     [function]
  syntax MInt ::= significandFloat(Float) [function, hook(FLOAT.significand)]

  syntax Float ::= fpNaN(Int, Int)              [smtlib((as NaN (_ FP #1 #2)))]
                 | plusInfinity(Int, Int)       [smtlib((as plusInfinity (_ FP #1 #2)))]
                 | minusInfinity(Int, Int)      [smtlib((as minusInfinity (_ FP #1 #2)))]

  syntax Float ::= "--Float" Float             [function, smtlib(-), hook(FLOAT.neg)]
                 > Float "^Float" Float        [function, left, latex({#1}^{#2}), hook(FLOAT.pow)]
                 > left:
                   Float "*Float" Float        [function, left, smtlib((* roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}), hook(FLOAT.mul)]
                 | Float "/Float" Float        [function, left, smtlib((/ roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}), hook(FLOAT.div)]
                 | Float "%Float" Float        [function, left, smtlib((remainder roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}), hook(FLOAT.rem)]
                 > left:
                   Float "+Float" Float        [function, left, smtlib((+ roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{+_{\scriptstyle\it Float}}{#2}), hook(FLOAT.add)]
                 | Float "-Float" Float        [function, left, smtlib((- roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{-_{\scriptstyle\it Float}}{#2}), hook(FLOAT.sub)]

  syntax Float ::= rootFloat(Float, Int)        [function, hook(FLOAT.root)]
                 | absFloat(Float)              [function, smtlib(abs), hook(FLOAT.abs)]
                 | roundFloat(Float, Int, Int)  [function, hook(FLOAT.round)]
                 | floorFloat(Float)            [function, hook(FLOAT.floor)]
                 | ceilFloat(Float)             [function, hook(FLOAT.ceil)]
                 | expFloat(Float)              [function, hook(FLOAT.exp)]
                 | logFloat(Float)              [function, hook(FLOAT.log)]
                 | sinFloat(Float)              [function, hook(FLOAT.sin)]
                 | cosFloat(Float)              [function, hook(FLOAT.cos)]
                 | tanFloat(Float)              [function, hook(FLOAT.tan)]
                 | asinFloat(Float)             [function, hook(FLOAT.asin)]
                 | acosFloat(Float)             [function, hook(FLOAT.acos)]
                 | atanFloat(Float)             [function, hook(FLOAT.atan)]
                 | atan2Float(Float, Float)     [function, hook(FLOAT.atan2)]
                 | maxFloat(Float, Float)       [function, smtlib(max), hook(FLOAT.max)]
                 | minFloat(Float, Float)       [function, smtlib(min), hook(FLOAT.min)]
                 | sqrtFloat(Float)             [function]
                 | maxValueFloat(Int, Int)      [function, hook(FLOAT.maxValue)]
                 | minValueFloat(Int, Int)      [function, hook(FLOAT.minValue)]

  syntax Bool ::= Float "<=Float" Float       [function, left, smtlib(<=), latex({#1}\mathrel{\leq_{\scriptstyle\it Float}}{#2}), hook(FLOAT.le)]
                | Float "<Float" Float        [function, left, smtlib(<), latex({#1}\mathrel{<_{\scriptstyle\it Float}}{#2}), hook(FLOAT.lt)]
                | Float ">=Float" Float       [function, left, smtlib(>=), latex({#1}\mathrel{\geq_{\scriptstyle\it Float}}{#2}), hook(FLOAT.ge)]
                | Float ">Float" Float        [function, left, smtlib(>), latex({#1}\mathrel{>_{\scriptstyle\it Float}}{#2}), hook(FLOAT.gt)]
                | Float "==Float" Float       [function, left, smtlib(==), latex({#1}\mathrel{==_{\scriptstyle\it Float}}{#2}), hook(FLOAT.eq), klabel(_==Float_)]
                | Float "=/=Float" Float      [function, left, smtlib((not (== #1 #2))), latex({#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2})]


  rule F1:Float =/=Float F2:Float => notBool (F1 ==Float F2)

  syntax Float ::= Int2Float(Int, Int, Int)    [function, latex({\\it{}Int2Float}), hook(FLOAT.int2float)]
  syntax Int ::= Float2Int(Float)    [function, latex({\\it{}Float2Int}), hook(FLOAT.float2int)]

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

module STRING
  imports STRING-SYNTAX
  imports INT
  imports FLOAT-SYNTAX
  imports K-EQUAL

  syntax String ::= String "+String" String    [function, left, latex({#1}+_{\scriptstyle\it String}{#2}), hook(STRING.concat)]

  syntax Bool ::= String "==String" String [function, left, hook(STRING.eq)]

  syntax Int ::= lengthString ( String ) [function, hook(STRING.length)]
  syntax String ::= chrChar ( Int )      [function, hook(STRING.chr)]
  syntax Int ::= ordChar ( String )      [function, hook(STRING.ord)]

  syntax String ::= substrString ( String , Int , Int ) [function, hook(STRING.substr)]
  syntax Int ::= findString ( String , String , Int )   [function, hook(STRING.find)]
  syntax Int ::= rfindString ( String , String , Int )  [function, hook(STRING.rfind)]
  syntax Int ::= findChar ( String , String , Int )     [function, hook(STRING.findChar)]
  syntax Int ::= rfindChar ( String , String , Int )    [function, hook(STRING.rfindChar)]

  syntax String ::= Float2String ( Float )              [function, hook(STRING.float2string)]
  syntax String ::= Float2String ( Float , String )     [function, klabel(FloatFormat), hook(STRING.floatFormat)]
  syntax Float  ::= String2Float ( String )             [function, hook(STRING.string2float)]
  syntax Int    ::= String2Int   ( String )             [function, hook(STRING.string2int)]
  syntax String ::= Int2String   ( Int )                [function, hook(STRING.int2string)]
  syntax String ::= Base2String  ( Int , Int )          [function, hook(STRING.base2string)]
  syntax Int    ::= String2Base  ( String , Int )       [function, hook(STRING.string2base)]


  syntax String ::= "replaceAll" "(" String "," String "," String ")"      [function, hook(STRING.replaceAll)]
  syntax String ::= "replace" "(" String "," String "," String "," Int ")" [function, hook(STRING.replace)]
  syntax String ::= "replaceFirst" "(" String "," String "," String ")"    [function, hook(STRING.replaceFirst)]
  syntax Int ::= "countAllOccurrences" "(" String "," String ")"            [function, hook(STRING.countAllOccurrences)]

  syntax Bool ::= String "=/=String" String      [function, left, hook(STRING.ne)]
  rule S1:String =/=String S2:String => notBool (S1 ==String S2)
  rule S1:String ==String S2:String => S1 ==K S2

  syntax Bool ::= String  "<String" String [function, hook(STRING.lt)]
                | String "<=String" String [function, hook(STRING.le)]
                | String  ">String" String [function, hook(STRING.gt)]
                | String ">=String" String [function, hook(STRING.ge)]

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

module STRING-BUFFER-SYNTAX
  imports BASIC-K
  imports STRING

  syntax StringBuffer [hook(BUFFER.StringBuffer)]
  syntax StringBuffer ::= ".StringBuffer" [function, hook(BUFFER.empty), impure]
  syntax StringBuffer ::= StringBuffer "+String" String [function, left, hook(BUFFER.concat), avoid]
  syntax String ::= StringBuffer2String ( StringBuffer ) [function, hook(BUFFER.toString)]
endmodule

module STRING-BUFFER-SYMBOLIC [symbolic]
  imports STRING-BUFFER-SYNTAX
  imports STRING-SYNTAX
  imports BOOL-SYNTAX

  syntax StringBuffer ::= String

  rule .StringBuffer => ""

  rule StringBuffer2String(S:String) => S
endmodule

module STRING-BUFFER
  imports STRING-BUFFER-SYNTAX
  imports STRING-BUFFER-SYMBOLIC
endmodule

module BYTES-SYNTAX
  syntax Bytes [hook(BYTES.Bytes)]

  syntax Bytes ::= ".Bytes" [function, hook(BYTES.empty), impure]
  syntax Endianness ::= "LE" [klabel(littleEndianBytes)]
                      | "BE" [klabel(bigEndianBytes)]
  syntax Signedness ::= "Signed" [klabel(signedBytes)]
                      | "Unsigned" [klabel(unsignedBytes)]
  syntax Int ::= Bytes2Int(Bytes, Endianness, Signedness) [function, hook(BYTES.bytes2int)]
  syntax Bytes ::= Int2Bytes(Int, Int, Endianness) [function, hook(BYTES.int2bytes)]
                 | Int2Bytes(Int, Endianness, Signedness) [function, klabel(Int2BytesNoLen)]
  syntax String ::= Bytes2String(Bytes) [function, hook(BYTES.bytes2string)]
  syntax Bytes ::= String2Bytes(String) [function, hook(BYTES.string2bytes)]

  syntax Bytes ::= substrBytes(Bytes, Int, Int) [function, hook(BYTES.substr)]
  syntax Bytes ::= replaceAtBytes(Bytes, Int, Bytes) [function, hook(BYTES.replaceAt)]
  syntax Bytes ::= padRightBytes(Bytes, Int, Int) [function, hook(BYTES.padRight)]
                 | padLeftBytes(Bytes, Int, Int) [function, hook(BYTES.padLeft)]
  syntax Bytes ::= reverseBytes(Bytes) [function, hook(BYTES.reverse)]

  syntax Int ::= lengthBytes(Bytes) [function, hook(BYTES.length), smtlib(lengthBytes)]

  syntax Bytes ::= Bytes "+Bytes" Bytes [function, hook(BYTES.concat), right]
endmodule

module BYTES-SYMBOLIC [symbolic]
  imports BYTES-SYNTAX
  imports INT
  imports K-EQUAL
  imports STRING
  imports STRING-BUFFER

  syntax Bytes ::= "nilBytes"
                 | Int ":" Bytes

  rule .Bytes => nilBytes

  rule Bytes2Int(nilBytes, _, _) => 0
  rule Bytes2Int(B : nilBytes, BE, Unsigned) => B
  rule Bytes2Int(B0 : B1 : BS, BE, Unsigned) => Bytes2Int(((B0 <<Int 8) |Int B1) : BS, BE, Unsigned)
  rule Bytes2Int(B0 : BS, BE, Signed) => signExtendBitRangeInt(Bytes2Int(B0 : BS, BE, Unsigned), 0, lengthBytes(B0 : BS) <<Int 3)
  rule Bytes2Int(B0 : BS, LE, S) => Bytes2Int(reverseBytes(B0 : BS), BE, S)

  syntax Bytes ::= Int2Bytes(Int, Bytes) [function, klabel(Int2BytesAux)]
  rule Int2Bytes(LEN, I, BE) => padLeftBytes(Int2Bytes(bitRangeInt(I, 0, LEN <<Int 3), nilBytes), LEN, #if I <Int 0 #then 255 #else 0 #fi)
  rule Int2Bytes(LEN, I, LE) => reverseBytes(Int2Bytes(LEN, I, BE))
  rule Int2Bytes(0, BS) => BS
  rule Int2Bytes(I, BS) => Int2Bytes(I >>Int 8, I &Int 255 : BS) requires I =/=Int 0

  syntax String ::= Bytes2String(Bytes, StringBuffer) [function, klabel(Bytes2StringAux)]
  rule Bytes2String(BS) => Bytes2String(BS, .StringBuffer)
  rule Bytes2String(nilBytes, BUFFER) => StringBuffer2String(BUFFER)
  rule Bytes2String(B : BS, BUFFER) => Bytes2String(BS, BUFFER +String chrChar(B))

  rule String2Bytes(S) => ordChar(substrString(S, 0, 1)) : String2Bytes(substrString(S, 1, lengthString(S))) requires lengthString(S) >=Int 1
  rule String2Bytes("") => nilBytes

  rule substrBytes(BS, 0, 0) => nilBytes
  rule substrBytes(B : BS, N, M) => substrBytes(BS, N -Int 1, M -Int 1) requires N >Int 0
  rule substrBytes(B : BS, 0, M) => B : substrBytes(BS, 0, M -Int 1) requires M >Int 0

  rule replaceAtBytes(BS, _, nilBytes) => BS
  rule replaceAtBytes(B : BS, N, BS') => B : replaceAtBytes(BS, N -Int 1, BS') requires N >Int 0
  rule replaceAtBytes(_ : BS, 0, B : BS') => B : replaceAtBytes(BS, 0, BS')

  rule padRightBytes(BS, LEN, VAL) => reverseBytes(padLeftBytes(reverseBytes(BS), LEN, VAL))
  rule padLeftBytes(BS, LEN, VAL) => BS requires lengthBytes(BS) >=Int LEN
  rule padLeftBytes(BS, LEN, VAL) => padLeftBytes(VAL : BS, LEN, VAL) requires lengthBytes(BS) <Int LEN

  syntax Bytes ::= reverseBytes(Bytes, Bytes) [function, klabel(reverseBytesAux)]
  rule reverseBytes(BS) => reverseBytes(BS, nilBytes)
  rule reverseBytes(nilBytes, BS) => BS
  rule reverseBytes(B : BS, BS') => reverseBytes(BS, B : BS')

  syntax Int ::= lengthBytes(Bytes, Int) [function, klabel(lengthBytesAux), smtlib(lengthBytesAux)]
  rule lengthBytes(BS) => lengthBytes(BS, 0)
  rule lengthBytes(nilBytes, SIZE) => SIZE
  rule lengthBytes(B : BS, SIZE) => lengthBytes(BS, SIZE +Int 1)

  rule nilBytes +Bytes B2 => B2
  rule (B : BS) +Bytes B2 => B : (BS +Bytes B2)
endmodule

module BYTES
  imports BYTES-SYNTAX
  imports BYTES-SYMBOLIC
  imports INT
  rule Int2Bytes(I, E, Unsigned) => Int2Bytes((log2Int(I) +Int 8) /Int 8, I, E)
    requires I >Int 0
  rule Int2Bytes(0, _::Endianness, _) => .Bytes
  rule Int2Bytes(I, E, Signed) => Int2Bytes((log2Int(I) +Int 9) /Int 8, I, E)
    requires I >Int 0
  rule Int2Bytes(I, E, Signed) => Int2Bytes((log2Int(~Int I) +Int 9) /Int 8, I, E)
    requires I <Int -1
  rule Int2Bytes(-1, E, Signed) => Int2Bytes(1, -1, E)
endmodule

module ID-PROGRAM-PARSING
  imports BUILTIN-ID-TOKENS
  syntax Id ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [prec(1), notInRules, token, autoReject]
              | #LowerId                                             [notInRules, token, autoReject]
              | #UpperId                                             [notInRules, token, autoReject]
endmodule

module ID-SYNTAX
  imports INT-SYNTAX
  imports STRING-SYNTAX

  syntax Id [token]

  syntax String ::= Id2String ( Id )    [function, hook(STRING.token2string)]
  syntax Id ::= String2Id (String) [function, hook(STRING.string2token)]
  syntax Id ::= freshId(Int)    [freshGenerator, function]
endmodule

module ID
  imports ID-SYNTAX
  imports ID-SYMBOLIC
  imports STRING

  rule freshId(I:Int) => String2Id("_" +String Int2String(I))
endmodule

module ID-SYMBOLIC [symbolic]
  imports ID-SYNTAX
  syntax KItem  ::= "#parseToken"  "(" String "," String ")"  [function, hook(STRING.parseToken)]
  rule String2Id(S:String) => {#parseToken("Id", S)}:>Id
endmodule

module K-EQUAL
  imports BOOL
  imports BASIC-K

  syntax Bool ::= left:
                    K "==K" K           [function, smtlib(=), hook(KEQUAL.eq), klabel(_==K_), symbol, latex({#1}\mathrel{=_K}{#2}), equalEqualK]
                | K "=/=K" K          [function, smtlib(distinct), hook(KEQUAL.ne), latex({#1}\mathrel{\neq_K}{#2}), notEqualEqualK]

  syntax priorities equalEqualK notEqualEqualK > boolOperation mlOp
  rule K1:K =/=K K2:K => notBool (K1 ==K K2)

  rule K1:Bool ==Bool K2:Bool => K1 ==K K2

  syntax K ::= "#if" Bool "#then" K "#else" K "#fi"   [function, smtlib(ite), hook(KEQUAL.ite), poly(0, 2, 3)]

  rule #if C:Bool #then B1 #else _ #fi => B1 requires C
  rule #if C:Bool #then _ #else B2 #fi => B2 requires notBool C

endmodule

module K-REFLECTION
  imports BASIC-K
  imports STRING

  syntax K ::= "#configuration" [function, impure, hook(KREFLECTION.configuration)]
  syntax String ::= #sort(K) [function, hook(KREFLECTION.sort)]
  syntax KItem ::= #fresh(String)   [function, hook(KREFLECTION.fresh), impure]
  syntax KItem ::= getKLabel(K)  [function, hook(KREFLECTION.getKLabel)]
  syntax Bool ::= #isConcrete(K) [function, hook(KREFLECTION.isConcrete)]

  syntax String ::= #getenv(String) [function, impure, hook(KREFLECTION.getenv)]

  // meaningful only for the purposes of compilation to a binary, otherwise
  // undefined
  syntax List ::= #argv() [function, hook(KREFLECTION.argv)]

endmodule

module K-IO
  imports LIST
  imports STRING

  syntax IOError ::= "#EOF" | "#noparse" | #unknownIOError(Int)
                   | "#E2BIG"
                   | "#EACCES"
                   | "#EAGAIN"
                   | "#EBADF"
                   | "#EBUSY"
                   | "#ECHILD"
                   | "#EDEADLK"
                   | "#EDOM"
                   | "#EEXIST"
                   | "#EFAULT"
                   | "#EFBIG"
                   | "#EINTR"
                   | "#EINVAL"
                   | "#EIO"
                   | "#EISDIR"
                   | "#EMFILE"
                   | "#EMLINK"
                   | "#ENAMETOOLONG"
                   | "#ENFILE"
                   | "#ENODEV"
                   | "#ENOENT"
                   | "#ENOEXEC"
                   | "#ENOLCK"
                   | "#ENOMEM"
                   | "#ENOSPC"
                   | "#ENOSYS"
                   | "#ENOTDIR"
                   | "#ENOTEMPTY"
                   | "#ENOTTY"
                   | "#ENXIO"
                   | "#EPERM"
                   | "#EPIPE"
                   | "#ERANGE"
                   | "#EROFS"
                   | "#ESPIPE"
                   | "#ESRCH"
                   | "#EXDEV"
                   | "#EWOULDBLOCK"
                   | "#EINPROGRESS"
                   | "#EALREADY"
                   | "#ENOTSOCK"
                   | "#EDESTADDRREQ"
                   | "#EMSGSIZE"
                   | "#EPROTOTYPE"
                   | "#ENOPROTOOPT"
                   | "#EPROTONOSUPPORT"
                   | "#ESOCKTNOSUPPORT"
                   | "#EOPNOTSUPP"
                   | "#EPFNOSUPPORT"
                   | "#EAFNOSUPPORT"
                   | "#EADDRINUSE"
                   | "#EADDRNOTAVAIL"
                   | "#ENETDOWN"
                   | "#ENETUNREACH"
                   | "#ENETRESET"
                   | "#ECONNABORTED"
                   | "#ECONNRESET"
                   | "#ENOBUFS"
                   | "#EISCONN"
                   | "#ENOTCONN"
                   | "#ESHUTDOWN"
                   | "#ETOOMANYREFS"
                   | "#ETIMEDOUT"
                   | "#ECONNREFUSED"
                   | "#EHOSTDOWN"
                   | "#EHOSTUNREACH"
                   | "#ELOOP"
                   | "#EOVERFLOW"

  syntax Int ::= "#open" "(" String ")" [function]
               | "#open" "(" String "," String ")" [function, hook(IO.open), impure]
               | "#tell" "(" Int ")" [function, hook(IO.tell), impure]
               | "#getc" "(" Int ")"             [function, hook(IO.getc), impure]
  syntax String ::= "#read" "(" Int "," Int ")"    [function, hook(IO.read), impure]

  syntax K ::= "#close" "(" Int ")" [function, hook(IO.close), impure]
             | "#seek" "(" Int "," Int ")" [function, hook(IO.seek), impure]
             | "#seekEnd" "(" Int "," Int ")" [function, hook(IO.seekEnd), impure]
             | "#putc" "(" Int "," Int ")"      [function, hook(IO.putc), impure]
             | "#write" "(" Int "," String ")" [function, hook(IO.write), impure]
             | "#lock" "(" Int "," Int ")" [function, hook(IO.lock), impure]
             | "#unlock" "(" Int "," Int ")" [function, hook(IO.unlock), impure]

  syntax KItem ::= "#stat" "(" String ")" [function, hook(IO.stat), impure]
                 | "#lstat" "(" String ")" [function, hook(IO.lstat), impure]
                 | "#opendir" "(" String ")" [function, hook(IO.opendir), impure]

  syntax KItem ::= #parse ( String , String ) [function, hook(IO.parse), impure]
  syntax KItem ::= #parseInModule(String, // input
                                  String, // start symbol
                                  String) // module name
                                  [function, hook(IO.parseInModule), impure]

  rule #open(S:String) => #open(S:String, "r+")

  syntax Int ::= "#stdin"   [function]
                | "#stdout" [function]
                | "#stderr" [function]

  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

  syntax Stream ::= #buffer(K)

// ------------------------------
// System

  syntax KItem ::= #system ( String ) [function, hook(IO.system), impure]
                 | "#systemResult" "(" Int /* exit code */ "," String /* stdout */ "," String /* stderr */ ")"

  syntax K ::= #logToFile(String, String) [function, hook(IO.log), impure, returnsUnit]

endmodule

// NOTE: DO NOT DIRECTLY IMPORT *-STREAM MODULES
// These stream modules will be automatically instantiated and implicitly imported
// into the main module when `stream` attributes appear in configuration cells.
// Only `Stream` productions and `[stream]` rules will be imported.
// The cell name will be replaced with the one of the main configuration.

module STDIN-STREAM
  imports K-IO

  syntax Stream ::= #istream(Int)
  syntax Stream ::= #parseInput(String, String)

  configuration <stdin> ListItem(#buffer($STDIN:String)) ListItem($IO:String) ListItem(#istream(#stdin)) </stdin>

  // read one character at a time until we read whitespace
  rule [stdinGetc]:
       <stdin>
       ListItem(#parseInput(_:String, Delimiters:String))
       ListItem(#buffer(S:String => S +String chrChar(#getc(N))))
       ListItem("on")
       ListItem(#istream(N:Int))
       </stdin>
    requires findChar(S, Delimiters, 0) ==Int -1 // [stdin]
       [stream]

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
       => ListItem(#parse(substrString(S, 0, findChar(S, Delimiters, 0)), Sort)))
       ListItem(#buffer(S:String => substrString(S,findChar(S, Delimiters, 0) +Int 1, lengthString(S))))
       _:List
       </stdin>
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool Sort =/=String "String"
       andBool Sort =/=String "Int"
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
       [stream]
  rule [stdoutBufferInt]:
       <stdout>
       ListItem(#ostream(_))
       ListItem(_)
       ListItem(#buffer(Buffer:String => Buffer +String Int2String(I)))
       (ListItem(I:Int) => .List)
       _:List
       </stdout>
       // [stdout, stderr]
       [stream]
  rule [stdoutBufferString]:
       <stdout>
       ListItem(#ostream(_))
       ListItem(_)
       ListItem(#buffer(Buffer:String => Buffer +String S))
       (ListItem(S:String) => .List)
       _:List
       </stdout>
       // [stdout, stderr]
       [stream]

  // Send first char from the buffer to the server
  rule [stdoutWrite]:
       <stdout>
       ListItem(#ostream({(.K => #write(N, S)) ~> N:Int}:>Int))
       ListItem("on")
       ListItem(#buffer(S:String => ""))
       _:List
       </stdout>
    requires S =/=String "" // [stdout, stderr]
       [stream]

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

module MINT
  imports INT
  imports K-EQUAL
  imports LIST

  syntax MInt [hook(MINT.MInt)]

  /*@\section{Description} The MInt implements machine integers of arbitrary
   * bit width represented in 2's complement. */

  /*@ Machine integer of bit width and value. */
  syntax MInt ::= mi(Int, Int)    [function, hook(MINT.constructor)]

  /*@ Function returning the bit width of this machine integer. */
  syntax Int ::= bitwidthMInt(MInt)   [function, hook(MINT.bitwidth)]

  /*@
   * Functions returning the signed and unsigned interpretations of this
   * machine integers.
   *   svalue  returns an integer between -2^(bitwidth - 1) and
   *           2^(bitwidth - 1) - 1
   *   uvalue  returns an integer between 0 and 2^bitwidth - 1
   */
  syntax Int ::= svalueMInt(MInt)     [function, hook(MINT.svalue)]
               | uvalueMInt(MInt)     [function, hook(MINT.uvalue), smtlib(bv2int)]

  /*@ Checks whether a machine integer is zero */
  syntax Bool ::= zeroMInt(MInt)    [function, hook(MINT.zero)]

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

  /*@
   * Projection functions for results of operations with overflow.
   * miInt(saddMInt(...))         returns the result of the operation (ignoring
   *                              overflow)
   * overflowMInt(saddMInt(...))  returns true if overflow is detected during
   *                              the execution of the operation
   */
  syntax MInt ::= miMInt(List)          [function]
  rule miMInt(ListItem(MI:MInt) ListItem(_:Bool)) => MI
  syntax Bool ::= overflowMInt(List)    [function]
  rule overflowMInt(ListItem(_:MInt) ListItem(B:Bool)) => B

  /*@
   * Arithmetic and comparison operations
   *   op   does not interprets the operands as either signed or unsigned
   *   sop  interprets the operands as signed
   *   uop  interprets the operands as unsigned
   */
  /*@
   * Addition, subtraction, and multiplication are the same for signed and
   * unsigned integers represented in 2's complement
   */
  syntax MInt ::= addMInt(MInt, MInt)   [function, hook(MINT.add), smtlib(bvadd)]
                | subMInt(MInt, MInt)   [function, hook(MINT.sub), smtlib(bvsub)]
                | mulMInt(MInt, MInt)   [function, hook(MINT.mul), smtlib(bvmul)]

  /*@
   * Division and reminder
   * sdiv/srem  operation interprets operands as signed; undefined if the second
   *            argument is 0; returns a pair of result and overflow flag
   *            represented as a list of 2 elements (overflow happens when the
   *            first operand is the minimum value and the second operand is -1)
   * udiv/urem  operation interprets operands as unsigned; undefined if the
   *            second argument is 0
   */
  syntax List ::= sdivMInt(MInt, MInt)    [function, hook(MINT.sdiv)]
                | sremMInt(MInt, MInt)    [function, hook(MINT.srem)]
  syntax MInt ::= udivMInt(MInt, MInt)    [function, hook(MINT.udiv), smtlib(bvudiv)]
                | uremMInt(MInt, MInt)    [function, hook(MINT.urem), smtlib(bvurem)]

  /*@
   * Addition, subtraction and multiplication with overflow detection; each
   * operation returns a pair of result and overflow flag represented as a list
   * of 2 elements
   */
  syntax List ::= saddMInt(MInt, MInt)    [function, hook(MINT.sadd)]
                | uaddMInt(MInt, MInt)    [function, hook(MINT.uadd)]
                | ssubMInt(MInt, MInt)    [function, hook(MINT.ssub)]
                | usubMInt(MInt, MInt)    [function, hook(MINT.usub)]
                | smulMInt(MInt, MInt)    [function, hook(MINT.smul)]
                | umulMInt(MInt, MInt)    [function, hook(MINT.umul)]

  /*@
   * Shift operations; the second operand must be non-negative
   *
   * ashrMInt   arithmetic shift: filling with leftmost bit (sign extension)
   * lshrMInt   logical shift: filling with zeros
   */
  syntax MInt ::= shlMInt(MInt, Int)    [function, hook(MINT.shl), smtlib(bvshl)]
                | ashrMInt(MInt, Int)   [function, hook(MINT.ashr)]
                | lshrMInt(MInt, Int)   [function, hook(MINT.lshr), smtlib(bvlshr)]

  /*@ Bitwise operations */
  syntax MInt ::= andMInt(MInt, MInt)   [function, hook(MINT.and), smtlib(bvand)]
                | orMInt(MInt, MInt)    [function, hook(MINT.or), smtlib(bvor)]
                | xorMInt(MInt, MInt)   [function, hook(MINT.xor), smtlib(bvxor)]

  syntax MInt ::= negMInt(MInt)   [function]
  rule negMInt(MI:MInt) => xorMInt(MI, mi(bitwidthMInt(MI), -1))

  /*@ Comparison operations */
  syntax Bool ::= sltMInt(MInt, MInt)   [function, hook(MINT.slt), smtlib(bvslt)]
                | ultMInt(MInt, MInt)   [function, hook(MINT.ult), smtlib(bvult)]
                | sleMInt(MInt, MInt)   [function, hook(MINT.sle), smtlib(bvsle)]
                | uleMInt(MInt, MInt)   [function, hook(MINT.ule), smtlib(bvule)]
                | sgtMInt(MInt, MInt)   [function, hook(MINT.sgt), smtlib(bvsgt)]
                | ugtMInt(MInt, MInt)   [function, hook(MINT.ugt), smtlib(bvugt)]
                | sgeMInt(MInt, MInt)   [function, hook(MINT.sge), smtlib(bvsge)]
                | ugeMInt(MInt, MInt)   [function, hook(MINT.uge), smtlib(bvuge)]
                | eqMInt(MInt, MInt)    [function, hook(MINT.eq), smtlib(=)]
                | neMInt(MInt, MInt)    [function, hook(MINT.ne), smtlib(distinct)]

  syntax MInt ::= sMaxMInt(MInt, MInt) [function, smtlib((ite (bvslt #1 #2) #2 #1))]
                | sMinMInt(MInt, MInt) [function, smtlib((ite (bvslt #1 #2) #1 #2))]

  /*@
   * Returns a machine integer with the underlying bits; the bits of the first
   * machine integer concatenated with the bits of the second machine integer.
   * The bits of the first machine integer are on the more significant
   * positions. The resulting bit width is the sum of two inputs' bit widths.
   */
  syntax MInt ::= concatenateMInt(MInt, MInt)   [function, hook(MINT.concatenate), smtlib((concat #2 #1))]

  /*@
   * Returns a machine integer with the underlying bits of the given
   * machine integer in the given range. The bit on position 0 is the most
   * significant bit.
   */
  syntax MInt ::= extractMInt(MInt, Int, Int)   [function, hook(MINT.extract), smtlib(extract)]

  /*@
   * digitsOfMInt(mInt, digitBitWidth, count)
   *
   * Returns a list of the first digits representing the given machine integer,
   * each digit a machine integer on the given bitwidth. Useful for serializing
   * a integer to a sequence of bytes.
   */
  syntax List ::= digitsOfMInt(MInt, Int, Int)   [function, hook(MINT.toDigits)]

  /*@
   * Returns a machine integer representing the given list of digits. Each digit
   * is represented as a machine integers. The list must be non-empty. Useful
   * for deserializing an integer from a sequence of bytes.
   */
  syntax MInt ::= mIntOfDigits(List)   [function, hook(MINT.fromDigits)]

  // TODO(AndreiS): change
  rule zeroMInt(MI:MInt) => eqMInt(MI, xorMInt(MI, MI))

  /*@
   * Conversion to and from a list of digits
   */
  rule
    digitsOfMInt(MI:MInt, N:Int, M:Int)
  =>
    digitsOfMInt(MI, N, M -Int 1)
    ListItem(extractMInt(MI, N *Int (M -Int 1), N *Int M))
  when M >Int 0
  rule digitsOfMInt(_:MInt, _:Int, 0) => .List

  rule
    mIntOfDigits(ListItem(MI1:MInt) ListItem(MI2:MInt) L:List)
  =>
    concatenateMInt(MI1, mIntOfDigits(ListItem(MI2) L))
  rule mIntOfDigits(ListItem(MI:MInt)) => MI
endmodule

module CONFIGURATION-PRIMITIVES
    syntax K ::= "#RESTORE_CONFIGURATION" "(" K ")"  [klabel(#RESTORE_CONFIGURATION)]
endmodule

module STRATEGY
    imports BUILTIN-ID-TOKENS

    syntax #RuleTag ::= #LowerId                           [token]
                      | #UpperId                           [token]

    syntax Strategy ::= #STUCK()

    syntax StrategyApply ::= "^" #RuleTag                      [klabel(#applyRule), symbol]

    syntax StrategyApplied ::= "~" #RuleTag                    [klabel(#appliedRule), symbol]

    syntax Strategy ::= StrategyApply | StrategyApplied

    configuration <s> $STRATEGY:K  </s>
endmodule

module DEFAULT-STRATEGY
    imports syntax STRATEGY

    rule ~ regular => ^ regular [anywhere]

    rule initSCell(_) => <s> ^ regular </s>
endmodule

module BASIC-STRATEGY
    imports STRATEGY
    imports BOOL
    imports CONFIGURATION-PRIMITIVES

    syntax Strategy ::= Bool

    syntax Hole ::= "#SHOLE" | "#FROZEN" "(" K ")"

    syntax Strategy ::= Hole

    syntax Strategy ::= "if" Strategy "then" Strategy "else" Strategy
                        > Strategy "*"
                        > Strategy ";" Strategy                             [right]
                        > Strategy "||" Strategy                            [right]


    rule <s> S:Strategy* => if S then S* else true ...</s>

    rule <s> A:Strategy || B:Strategy => A ~> #FROZEN(THIS_CONFIGURATION:K) ~> #SHOLE || B ...</s> when notBool(isBool(A))
    rule <s> A:Bool ~> #SHOLE || B:Strategy => A || B ...</s>
    rule <s> false || B:Strategy => B ...</s>
    rule <s> true || B:Strategy => true ...</s>

    rule <s> if true then B:Strategy else C:Strategy => B ...</s>
    rule <s> if false then B:Strategy else C:Strategy => C ...</s>

    rule <s> if A:Strategy then B:Strategy else C:Strategy => (A ~> #FROZEN(THIS_CONFIGURATION:K) ~> if #SHOLE then B else C) ...</s> when notBool(isBool(A))
    rule <s> A:Bool ~> if #SHOLE then B:Strategy else C:Strategy => if A then B else C ...</s>

    rule <s> false ~> #FROZEN(CONFIGURATION:K) => #RESTORE_CONFIGURATION(CONFIGURATION) ~> false  ...</s>

    rule <s> true ~> #FROZEN(CONFIGURATION:K) => true ...</s>

//    rule <s> #STUCK ~> X:StrategyApply => false ...</s>
    rule <s> X:StrategyApplied => true ...</s>

    rule <s> A:Strategy ; B:Strategy => A ~> #SHOLE ; B ...</s> when notBool(isBool(A))

    rule <s> A:Bool ~> #SHOLE ; B:Strategy => A ; B ...</s>

    rule <s> true ; B:Strategy => B ...</s>

    rule <s> false ; B:Strategy => false ...</s>

// the second rule is stupid -- just made to sidestep what is likely a KSEQ normalization bug
    rule <s> #STUCK() ~> A:StrategyApply => false ...</s>
    rule <s> #STUCK() ~> false => false ...</s>

endmodule
