// Copyright (c) 2015 K Team. All Rights Reserved.
module DOMAINS-COMMON
  imports EMPTY-ID
  imports INT-SYNTAX
  imports BOOL-SYNTAX
  imports STRING-SYNTAX
endmodule

module DOMAINS-SYNTAX
  imports DOMAINS-COMMON
  imports ID
endmodule

module DOMAINS
  imports INT
  imports BOOL
  imports STRING
  imports K
  imports K-IO
  imports LIST
  imports MAP
  imports SET
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
  syntax Map ::= Map Map                        [left, function, hook(MAP.concat), klabel('_Map_), assoc, comm, unit(.Map), element(_|->_)]
  /*@  Construct an empty Map */
  syntax Map ::= ".Map"                         [function, hook(MAP.unit), latex(\dotCt{Map})]
               // breaks klabel uniqueness
               //| "."                            [function, hook(MAP.unit)]
  syntax Map ::= "(" Map ")" [bracket]
  /*@ Construct a singleton Map (a Map with only one key/value pair). The key
   is on the left and the value is on the right */
  syntax Map ::= K "|->" K                      [function, hook(MAP.element), latex({#1}\mapsto{#2})]

  syntax priorities '_|->_ > '_Map_ '.Map

  /*@ Retrieve the value associated with the given key */
  syntax K ::= Map "[" K "]"                    [function, hook(MAP.lookup), klabel(Map:lookup)]

  /*@ Update a Map in form of  of keys and values: */
  syntax Map ::= Map "[" K "<-" K "]"           [function, hook(MAP.update), prefer]

  /*@ Remove key/value pair associated with the key from map? */
  syntax Map ::= Map "[" K "<-" "undef" "]"     [function, hook(MAP.remove)]

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

  syntax Bool ::= K "in_keys" "(" Map ")"       [function, hook(MAP.in_keys)]

  /*@ Get a List consisting of all values in the Map: */
  syntax List ::= values(Map)                   [function, hook(MAP.values)]

  /*@ Get the Map size (number of key/value pairs) */
  syntax Int ::= size(Map)                      [function, hook(MAP.size), klabel('sizeMap)]

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
  syntax Set ::= Set Set                  [left, function, hook(SET.concat), klabel('_Set_), assoc, comm, unit(.Set), idem, element(SetItem)]
  /*@ Construct an empty Set */
  syntax Set ::= ".Set"                   [function, hook(SET.unit), latex(\dotCt{Set})]
               //| "."
  /*@ Construct a singleton Set (a Set with only one element $\{ a \}$). To add
   an element $a$ to a set $A$, construct the union of the singleton set
   $\{ a \}$ and $A$ ($\{ a \} \cup A$). */
  syntax Set ::= SetItem(K)               [function, hook(SET.element)]

  /*@ Get the intersection of two sets ($A \cap B$) */
  syntax Set ::= intersectSet(Set, Set)   [function, hook(SET.intersection)]

  /*@ Get the difference of two sets ($A \setminus B$)*/
  syntax Set ::= Set "-Set" Set           [function, hook(SET.difference), latex({#1}-_{\it Set}{#2})]

  /*@ Check element membership in a set ($a \in A$) */
  syntax Bool ::= K "in" Set              [function, hook(SET.in)]

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
  syntax List ::= List List               [left, function, hook(LIST.concat), klabel('_List_), smtlib(smt_seq_concat), assoc, unit(.List), element(ListItem)]
  /*@ Construct an empty List: */
  syntax List ::= ".List"                 [function, hook(LIST.unit), smtlib(smt_seq_nil), latex(\dotCt{List})]
                //| "."
  /*@ Construct a singleton List (a list with only  one element) */
  syntax List ::= ListItem(K)             [function, hook(LIST.element), smtlib(smt_seq_elem)]

  /*@ Get an element form the List by index. Positive indices mean from the
   beginning (0 is the first element), and negative indices mean from the end
   (-1 is the last element). */
  syntax K ::= List "[" Int "]"           [function, hook(LIST.get), klabel(List:get)]

  /*@ Remove elements from the beginning and the end of the List. */
  syntax List ::= range(List, Int, Int)   [function, hook(LIST.range), klabel(List:range)]

  /*@ Check element membership in the given list */
  syntax Bool ::= K "in" List             [function, hook(LIST.in), klabel('_inList_)]

  /*@ Get the list length */
  syntax Int ::= size(List)               [function, hook(LIST.size), klabel ('sizeList), smtlib(smt_seq_len)]
endmodule

module BOOL-SYNTAX
  syntax Bool [hook(BOOL.Bool)]
  syntax Bool ::= "true"  [token]
  syntax Bool ::= "false" [token]
endmodule

module BOOL
  imports BASIC-K
  imports BOOL-SYNTAX
  syntax Bool ::= "notBool" Bool          [function, smtlib(not), boolOperation, latex(\neg_{\scriptstyle\it Bool}{#1}), hook(BOOL.not)]
                > Bool "andBool" Bool     [function, left, smtlib(and), boolOperation, latex({#1}\wedge_{\scriptstyle\it Bool}{#2}), hook(BOOL.and)]
                | K "andThenBool" K       [function, left, smtlib(and), boolOperation, hook(BOOL.andThen)]
                > Bool "xorBool" Bool     [function, left, smtlib(xor), boolOperation, hook(BOOL.xor)]
                > Bool "orBool" Bool      [function, left, smtlib(or), boolOperation, latex({#1}\vee_{\scriptstyle\it Bool}{#2}), hook(BOOL.or)]
                | K "orElseBool" K        [function, left, smtlib(or), boolOperation, hook(BOOL.orElse)]
                > Bool "impliesBool" Bool [function, left, smtlib(=>), boolOperation, hook(BOOL.implies)]
                > left:
                  Bool "==Bool" Bool      [function, left, smtlib(=), hook(BOOL.eq)]
                | Bool "=/=Bool" Bool     [function, left, smtlib(distinct), hook(BOOL.ne)]

  rule notBool true => false
  rule notBool false => true

  rule true andBool B:Bool => B:Bool
  rule B:Bool andBool true => B:Bool
  rule false andBool _:Bool => false
  rule _:Bool andBool false => false

  rule true andThenBool K:K => K
  rule K:K andThenBool true => K
  rule false andThenBool _ => false
  rule _ andThenBool false => false

  rule false xorBool B:Bool => B:Bool
  rule B:Bool xorBool false => B:Bool
  rule B:Bool xorBool B:Bool => false
  rule B1:Bool xorBool B2:Bool => notBool `B1 ==Bool B2`

  rule true orBool _:Bool => true
  rule _:Bool orBool true => true
  rule false orBool B:Bool => B
  rule B:Bool orBool false => B

  rule true orElseBool _ => true
  rule _ orElseBool true => true
  rule false orElseBool K:K => K
  rule K:K orElseBool false => K

  rule true impliesBool B:Bool => B
  rule false impliesBool _:Bool => true
  rule _:Bool impliesBool true => true
  rule B:Bool impliesBool false => notBool B

  rule B1:Bool =/=Bool B2:Bool => notBool `B1 ==Bool B2`

endmodule

module INT-SYNTAX
  syntax Int [hook(INT.Int)]
  syntax Int ::= r"[\\+-]?[0-9]+" [prefer, token]
endmodule

module INT
  imports INT-SYNTAX
  imports BOOL
  imports K-EQUAL

  syntax Int ::= "~Int" Int                     [function, latex(\mathop{\sim_{\scriptstyle\it Int}}{#1}), hook(INT.not)]
               > left:
                 Int "^Int" Int                 [function, left, latex({#1}\mathrel{{\char`\^}_{\!\scriptstyle\it Int}}{#2}), hook(INT.pow)]
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
               | "absInt" "(" Int ")"           [function, smtlib(int_abs), klabel(absInt), hook(INT.abs)]

  rule I1:Int divInt I2:Int => `I1 -Int `I1 modInt I2`` /Int I2
  requires I2 =/=Int 0
  rule
    I1:Int modInt I2:Int
  =>
    ``I1 %Int absInt(I2)` +Int absInt(I2)` %Int absInt(I2)
  requires I2 =/=Int 0

  syntax Bool ::= Int "<=Int" Int         [function, left, smtlib(<=), latex({#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}), hook(INT.le)]
                | Int "<Int" Int          [function, left, smtlib(<), latex({#1}\mathrel{<_{\scriptstyle\it Int}}{#2}), hook(INT.lt)]
                | Int ">=Int" Int         [function, left, smtlib(>=), latex({#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}), hook(INT.ge)]
                | Int ">Int" Int          [function, left, smtlib(>), latex({#1}\mathrel{>_{\scriptstyle\it Int}}{#2}), hook(INT.gt)]
                | Int "==Int" Int         [function, left, smtlib(=), latex({#1}\mathrel{{=}{=}_{\scriptstyle\it Int}}{#2}), hook(INT.eq)]
                | Int "=/=Int" Int        [function, left, smtlib(distinct), latex({#1}\mathrel{{=}{/}{=}_{\scriptstyle\it Int}}{#2}), hook(INT.ne)]
                | Int "dividesInt" Int    [function]

  rule I1:Int ==Int I2:Int => I1 ==K I2
  rule I1:Int =/=Int I2:Int => notBool `I1 ==Int I2`
  rule `I1:Int dividesInt I2:Int` => `I2 %Int I1` ==Int 0

  syntax Int ::= freshInt(Int)    [freshGenerator, function]
  rule freshInt(I:Int) => I

  syntax Int ::= randInt(Int) [function, hook(INT.rand)]
  syntax K ::= srandInt(Int) [function, hook(INT.srand)]
endmodule

module FLOAT-SYNTAX
  syntax Float [hook(FLOAT.Float)]
  syntax Float ::= r"([\\+-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+-]?([0-9]+(\\.[0-9]*)?|\\.[0-9]d+))?([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token]
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
                | Float "==Float" Float       [function, left, smtlib(==), latex({#1}\mathrel{==_{\scriptstyle\it Float}}{#2}), hook(FLOAT.eq)]
                | Float "=/=Float" Float      [function, left, smtlib((not (== #1 #2))), latex({#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2})]


  rule F1:Float =/=Float F2:Float => notBool `F1 ==Float F2`

  syntax Float ::= Int2Float(Int, Int, Int)    [function, klabel(Int2Float), latex({\\it{}Int2Float}), hook(FLOAT.int2float)]
  syntax Int ::= Float2Int(Float)    [function, klabel(Float2Int), latex({\\it{}Float2Int}), hook(FLOAT.float2int)]

  rule sqrtFloat(F:Float) => rootFloat(F, 2)

  rule isInfinite(F:Float) => F >Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F)) orBool F <Float --Float maxValueFloat(precisionFloat(F), exponentBitsFloat(F))

endmodule

module STRING-SYNTAX
  imports BASIC-K

  // Double Quoted Strings are of the form:
  // DoubleQuote StringChar* DoubleQuote
  // StringChar ::= ~[\"\n\r\\] // anything except for Newline, DoubleQuote and Backslash
  //              | [\\][nrtf\"\\] // Backslash followed by either 'nrtf', DoubleQuote or Backslash
  //              | [\\][x] 2*Hex // "\xFF"       Backslash 'x' followed by two   hexadecimal characters
  //              | [\\][u] 4*Hex // "\uFFFF"     Backslash 'u' followed by four  hexadecimal characters
  //              | [\\][U] 8*Hex // "\UFFffFFff" Backslash 'U' followed by eight hexadecimal characters
  //                              // the code must not be in the range [0xdfff, 0xd800] or exceed 0x10ffff
  syntax String [hook(STRING.String)]
  syntax String ::= r"[\\\"](([^\\\"\n\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][U][0-9a-fA-F]{8}))*[\\\"]"      [token]
endmodule

module STRING
  imports STRING-SYNTAX
  imports INT
  imports FLOAT-SYNTAX
  imports K-EQUAL

  syntax String ::= String "+String" String    [function, left, latex({#1}+_{\scriptstyle\it String}{#2}), hook(STRING.concat)]

  syntax Bool ::= String "==String" String [function, left, hook(STRING.eq)]

  syntax Int ::= "lengthString" "(" String ")" [function, klabel(lengthString), hook(STRING.length)]
  syntax String ::= "chrChar" "(" Int ")"      [function, klabel(chrChar), hook(STRING.chr)]
  syntax Int ::= "ordChar" "(" String ")"      [function, klabel(ordChar), hook(STRING.ord)]

  syntax String ::= "substrString" "(" String "," Int "," Int ")" [function, klabel(substrString), hook(STRING.substr)]
  syntax Int ::= "findString" "(" String "," String "," Int ")"   [function, klabel(findString), hook(STRING.find)]
  syntax Int ::= "rfindString" "(" String "," String "," Int ")"  [function, klabel(rfindString), hook(STRING.rfind)]
  syntax Int ::= "findChar" "(" String "," String "," Int ")"     [function, klabel(findChar), hook(STRING.findChar)]
  syntax Int ::= "rfindChar" "(" String "," String "," Int ")"    [function, klabel(rfindChar), hook(STRING.rfindChar)]

  syntax String ::= "Float2String" "(" Float ")"            [function, klabel(Float2String), hook(STRING.float2string)]
  syntax String ::= "Float2String" "(" Float "," String ")" [function, klabel(FloatFormat), hook(STRING.floatFormat)]
  syntax Float  ::= "String2Float" "(" String ")"           [function, klabel(String2Float), hook(STRING.string2float)]
  syntax Int    ::= "String2Int"   "(" String ")"           [function, klabel(String2Int), hook(STRING.string2int)]
  syntax String ::= "Int2String"   "(" Int ")"              [function, klabel(Int2String), hook(STRING.int2string)]
  syntax String ::= "Base2String"  "(" Int "," Int ")"      [function, klabel(Base2String), hook(STRING.base2string)]
  syntax Int    ::= "String2Base"  "(" String "," Int ")"   [function, klabel(String2Base), hook(STRING.string2base)]


  syntax String ::= "replaceAll" "(" String "," String "," String ")"      [function, hook(STRING.replaceAll)]
  syntax String ::= "replace" "(" String "," String "," String "," Int ")" [function, hook(STRING.replace)]
  syntax String ::= "replaceFirst" "(" String "," String "," String ")"    [function, hook(STRING.replaceFirst)]
  syntax Int ::= "countAllOccurrences" "(" String "," String ")"            [function, hook(STRING.countAllOccurrences)]

  syntax Bool ::= String "=/=String" String      [function, left, hook(STRING.ne)]
  rule S1:String =/=String S2:String => notBool `S1 ==String S2`
  rule S1:String ==String S2:String => S1 ==K S2

  syntax Bool ::= String  "<String" String [function, hook(STRING.lt)]
                | String "<=String" String [function, hook(STRING.le)]
                | String  ">String" String [function, hook(STRING.gt)]
                | String ">=String" String [function, hook(STRING.ge)]

  syntax String ::= categoryChar(String)       [function, hook(STRING.category)]
                  | directionalityChar(String) [function, hook(STRING.directionality)]

  rule S1:String <=String S2:String => notBool `S2 <String S1`
  rule S1:String >String S2:String => S2 <String S1
  rule S1:String >=String S2:String => notBool `S1 <String S2`

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

module ID
  syntax Id ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_]*"     [notInRules, token, autoReject]
endmodule

module EMPTY-ID
  syntax Id
endmodule

module K-EQUAL
  imports BOOL
  imports BASIC-K

  syntax Bool ::= left:
                    K "==K" K           [function, smtlib(=), hook(KEQUAL.eq), latex({#1}\mathrel{=_K}{#2}), equalEqualK]
                | K "=/=K" K          [function, smtlib(distinct), hook(KEQUAL.ne), latex({#1}\mathrel{\neq_K}{#2}), notEqualEqualK]

  syntax priorities equalEqualK notEqualEqualK > boolOperation
  rule K1:K =/=K K2:K => notBool `K1 ==K K2`

  rule K1:Bool ==Bool K2:Bool => K1 ==K K2

  syntax K ::= "#if" Bool "#then" K "#else" K "#fi"   [function, hook(KEQUAL.ite)]
  rule #if true #then K:K #else _:K #fi => K
  rule #if false #then _:K #else K:K #fi => K

endmodule

module K-REFLECTION
  imports BASIC-K
  imports STRING

  syntax K ::= "#configuration" [function, impure, hook(KREFLECTION.configuration)]
  syntax String ::= #sort(K) [function, hook(KREFLECTION.sort)]
  syntax KItem ::= #fresh(String)   [function, hook(KREFLECTION.fresh), impure]
  syntax KItem ::= getKLabel(K)  [function, hook(KREFLECTION.getKLabel)]

  // meaningful only for the purposes of compilation to a binary, otherwise
  // undefined
  syntax List ::= "#argv" [function, hook(KREFLECTION.argv)]

endmodule

module K-IO
  imports LIST
  imports STRING

  syntax IOError ::= "#EOF" | "#noparse" | "#ENOENT" | "#ENOTDIR" | "#EACCES" | "#ELOOP" | "#ENAMETOOLONG" | "#EBADF" | "#ESPIPE" | "#EISDIR" | "#EINVAL"

  syntax Int ::= "#open" "(" String ")" [function]
               | "#open" "(" String "," String ")" [function, hook(IO.open), impure]
               | "#tell" "(" Int ")" [function, hook(IO.tell), impure]
               | "#getc" "(" Int ")"             [function, hook(IO.getc), impure]
  syntax String ::= "#read" "(" Int "," Int ")"    [function, hook(IO.read), impure]

  syntax K ::= "#close" "(" Int ")" [function, hook(IO.close), impure]
             | "#seek" "(" Int "," Int ")" [function, hook(IO.seek), impure]
             | "#putc" "(" Int "," Int ")"      [function, hook(IO.putc), impure]
             | "#write" "(" Int "," String ")" [function, hook(IO.write), impure]

  syntax KItem ::= "#stat" "(" String ")" [function, hook(IO.stat), impure]
                 | "#lstat" "(" String ")" [function, hook(IO.lstat), impure]
                 | "#opendir" "(" String ")" [function, hook(IO.opendir), impure]

  syntax KItem ::= "#parse" "(" String "," String ")" [function, klabel(#parse), hook(IO.parse), impure]
  syntax KItem ::= #parseInModule(String, // input
                                  String, // start symbol
                                  String) // module name
                                  [function, hook(IO.parseInModule), impure]

  rule #open(S:String) => #open(S:String, "rw")

  syntax Int ::= "#stdin"   [function]
                | "#stdout" [function]
                | "#stderr" [function]

  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

  syntax Stream ::= #buffer(K)

// ------------------------------
// System

  syntax KItem ::= "#system" "(" String ")" [function, klabel(#system), hook(IO.system), impure]
                 | "#systemResult" "(" Int /* exit code */ "," String /* stdout */ "," String /* stderr */ ")"

endmodule

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

  // when we reach whitespace, if it parses create a ListItem
  rule [stdinParseString]:
       <stdin>
       `ListItem(#parseInput("String", Delimiters:String)) => ListItem(S)`
       ListItem(#buffer(S:String => ""))
       _:List
       </stdin>
    requires findChar(S, Delimiters, 0) =/=Int -1 // [stdin]

  // a hack: handle the case when we read integers without the help of the IO server
  rule [stdinParseInt]:
       <stdin>
       `ListItem(#parseInput("Int", Delimiters:String))
       => ListItem(String2Int(substrString(S, 0, findChar(S, Delimiters, 0))))`
       ListItem(#buffer(S:String => substrString(S,findChar(S, Delimiters, 0) +Int 1, lengthString(S))))
       _:List
       </stdin>
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool lengthString(S) >Int 1 // [stdin]

  rule [stdinParseArbitrarySort]:
       <stdin>
       `ListItem(#parseInput(Sort:String, Delimiters:String))
       => ListItem(#parse(substrString(S, 0, findChar(S, Delimiters, 0)), Sort))`
       ListItem(#buffer(S:String => substrString(S,findChar(S, Delimiters, 0) +Int 1, lengthString(S))))
       _:List
       </stdin>
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool Sort =/=String "String"
       andBool Sort =/=String "Int"
       andBool lengthString(S) >Int 1 // [stdin]

  rule [stdinTrim]:
       <stdin>
       ListItem(#parseInput(Sort:String, Delimiters:String))
       ListItem(#buffer(S:String => substrString(S, 1, lengthString(S))))
       _:List
       </stdin>
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool Sort =/=String "String"
       andBool lengthString(S) <=Int 1 // [stdin]

  /*
  syntax Stream ::= "#noIO"

  rule ListItem(#buffer(_))
       `ListItem(#noIO) ListItem(#istream(_:Int)) => .List` [stdin]
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
       `ListItem(F:Float) => .List`
       _:List
       </stdout>
       // [stdout, stderr]
  rule [stdoutBufferInt]:
       <stdout>
       ListItem(#ostream(_))
       ListItem(_)
       ListItem(#buffer(Buffer:String => Buffer +String Int2String(I)))
       `ListItem(I:Int) => .List`
       _:List
       </stdout>
       // [stdout, stderr]
  rule [stdoutBufferString]:
       <stdout>
       ListItem(#ostream(_))
       ListItem(_)
       ListItem(#buffer(Buffer:String => Buffer +String S))
       `ListItem(S:String) => .List`
       _:List
       </stdout>
       // [stdout, stderr]

  // Send first char from the buffer to the server
  rule [stdoutWrite]:
       <stdout>
       ListItem(#ostream(`.K => #write(N, S)` ~> N:Int))
       ListItem("on")
       ListItem(#buffer(S:String => ""))
       _:List
       </stdout>
    requires S =/=String "" // [stdout, stderr]

  /*
  syntax Stream ::= "#noIO"

  rule ListItem(#buffer(Buffer:String => Buffer +String Float2String(F)))
       `ListItem(F:Float) => .List`
       _:List [stdout, stderr]
  rule ListItem(#buffer(Buffer:String => Buffer +String Int2String(I)))
       `ListItem(I:Int) => .List`
       _:List [stdout, stderr]
  rule ListItem(#buffer(Buffer:String => Buffer +String S))
       `ListItem(S:String) => .List`
       _:List [stdout, stderr]

  rule `ListItem(#ostream(_:Int)) ListItem(#noIO) => .List`
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
  rule sminMInt(N:Int) => 0 -Int `1 <<Int `N -Int 1``
  rule smaxMInt(N:Int) => `1 <<Int `N -Int 1`` -Int 1
  rule uminMInt(_:Int) => 0
  rule umaxMInt(N:Int) => `1 <<Int N` -Int 1

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
  rule negMInt(MI:MInt) => xorMInt(MI, mi(bitwidthMInt(MI), 0))

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
    ListItem(extractMInt(MI, N *Int `M -Int 1`, N *Int M))
  when M >Int 0
  rule digitsOfMInt(_:MInt, _:Int, 0) => .List

  rule
    mIntOfDigits(ListItem(MI1:MInt) ListItem(MI2:MInt) L:List)
  =>
    concatenateMInt(MI1, mIntOfDigits(ListItem(MI2) L))
  rule mIntOfDigits(ListItem(MI:MInt)) => MI
endmodule
