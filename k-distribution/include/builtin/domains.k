// Copyright (c) 2015 K Team. All Rights Reserved.
module MAP
  imports LIST
  imports SET

  /*@\section{Description} The Map represents a generalized associative array.
   Each key can be paired with an arbitrary value, and can be used to reference
   its associated value. Multiple bindings for the same key are not allowed. */

  /*@ Construct a new Map consisting of key/value pairs of two Maps (the keys of
   the two Maps are assumed disjoint) */
  syntax Map ::= Map Map                        [left, function, hook(Map:__), klabel('_Map_), assoc, comm, unit(.Map), element(_|->_)]
  /*@  Construct an empty Map */
  syntax Map ::= ".Map"                         [function, hook(Map:.Map), latex(\dotCt{Map})]
               // breaks klabel uniqueness
               //| "."                            [function, hook(Map:.Map)]
  /*@ Construct a singleton Map (a Map with only one key/value pair). The key
   is on the left and the value is on the right */
  syntax Map ::= K "|->" K                      [function, hook(Map:_|->_), latex({#1}\mapsto{#2})]

  syntax priorities '_|->_ > '_Map_ '.Map

  /*@ Retrieve the value associated with the given key */
  syntax K ::= Map "[" K "]"                    [function, hook(Map:lookup), klabel(Map:lookup)]

  /*@ Update a Map in form of  of keys and values: */
  syntax Map ::= Map "[" K "<-" K "]"           [function, hook(Map:update), prefer]

  /*@ Remove key/value pair associated with the key from map? */
  syntax Map ::= Map "[" K "<-" "undef" "]"     [function, hook(Map:remove)]

  /*@ Get the difference of two maps interpreted as sets of entries
   ($M_1 \setminus M2$) */
  syntax Map ::= Map "-Map" Map                 [function, hook(Map:difference), latex({#1}-_{\it Map}{#2})]

  /*@ Update the first map by adding all key/value pairs in the second map. If a
   key in the first map exists also in the second map, its associated value will
   be overwritten by the value from the second map. */
  syntax Map ::= updateMap(Map, Map)            [function, hook(Map:updateAll)]

  /*@ Update the Map by removing all key/value pairs with the key in the Set. */
  syntax Map ::= removeAll(Map, Set)            [function, hook(Map:removeAll)]

  /*@ Get a Set consisting of all keys in the Map:*/
  syntax Set ::= keys(Map)                      [function, hook(Map:keys)]

  /*@ Get a List consisting of all values in the Map: */
  syntax List ::= values(Map)                   [function, hook(Map:values)]

  /*@ Get the Map size (number of key/value pairs) */
  syntax Int ::= size(Map)                      [function, hook(Collection:size), klabel('sizeMap)]

  /*@ Check map inclusion */
  syntax Bool ::= Map "<=Map" Map               [function, hook(Map:inclusion)]

  /*@ Get an arbitrarily chosen key of the Map  */
  syntax K ::= choice(Map)                      [function, hook(Map:choice), klabel(Map:choice)]
endmodule

module SET
  imports INT-SYNTAX
  imports BASIC-K

  /*@ \section{Description} The Set represents a mathematical set (a collection
   of unique items). */

  /*@ Construct a new Set as the union of two different sets ($A \cup B$) */
  syntax Set ::= Set Set                  [left, function, hook(Set:__), klabel('_Set_), assoc, comm, unit(.Set), idem, element(SetItem)]
  /*@ Construct an empty Set */
  syntax Set ::= ".Set"                   [function, hook(Set:.Set), latex(\dotCt{Set})]
               //| "."
  /*@ Construct a singleton Set (a Set with only one element $\{ a \}$). To add
   an element $a$ to a set $A$, construct the union of the singleton set
   $\{ a \}$ and $A$ ($\{ a \} \cup A$). */
  syntax Set ::= SetItem(K)               [function, hook(Set:SetItem)]

  /*@ Get the intersection of two sets ($A \cap B$) */
  syntax Set ::= intersectSet(Set, Set)   [function, hook(Set:intersection)]

  /*@ Get the difference of two sets ($A \setminus B$)*/
  syntax Set ::= Set "-Set" Set           [function, hook(Set:difference), latex({#1}-_{\it Set}{#2})]

  /*@ Check element membership in a set ($a \in A$) */
  syntax Bool ::= K "in" Set              [function, hook(Set:in)]

  /*@ Check set inclusion ($A \subseteq B$) */
  syntax Bool ::= Set "<=Set" Set         [function, hook(Set:inclusion)]

  /*@ Get the cardinality of a set ($|A|$) */
  syntax Int ::= size(Set)                [function, hook(Collection:size)]

  /*@ Get an arbitrarily chosen element of the Set */
  syntax K ::= choice(Set)                [function, hook(Set:choice), klabel(Set:choice)]

  /* set difference axioms */
  // TODO(AndreiS): remove this if not used
  //rule S1:Set -Set (SetItem(K:K) S2:Set) => S1 -Set S2
  //requires notBool(K in S1)
  //rule S:Set -Set .Set => S
endmodule

module LIST
  imports INT-SYNTAX
  imports BASIC-K

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
  syntax List ::= List List               [left, function, hook(List:__), klabel('_List_), smtlib(smt_seq_concat), assoc, unit(.List), element(ListItem)]
  /*@ Construct an empty List: */
  syntax List ::= ".List"                 [function, hook(List:.List), smtlib(smt_seq_nil), latex(\dotCt{List})]
                //| "."
  /*@ Construct a singleton List (a list with only  one element) */
  syntax List ::= ListItem(K)             [function, hook(List:ListItem), smtlib(smt_seq_elem)]

  /*@ Get an element form the List by index. Positive indices mean from the
   beginning (0 is the first element), and negative indices mean from the end
   (-1 is the last element). */
  syntax K ::= List "[" Int "]"           [function, hook(List:get), klabel(List:get)]

  /*@ Remove elements from the beginning and the end of the List. */
  syntax List ::= range(List, Int, Int)   [function, hook(List:range), klabel(List:range)]

  /*@ Check element membership in the given list */
  syntax Bool ::= K "in" List             [function, hook(List:in), klabel('_inList_)]

  /*@ Get the list length */
  syntax Int ::= size(List)               [function, hook(Collection:size), klabel ('sizeList), smtlib(smt_seq_len)]
endmodule

module BOOL-SYNTAX
  syntax Bool [hook(#BOOL)]
  syntax Bool ::= "true"  [token]
  syntax Bool ::= "false" [token]
endmodule

module BOOL
  imports KSEQ
  imports BOOL-SYNTAX
  syntax Bool ::= "notBool" Bool          [function, smtlib(not), boolOperation, latex(\neg_{\scriptstyle\it Bool}{#1}), hook(#BOOL:notBool_)]
                > Bool "andBool" Bool     [function, left, smtlib(and), boolOperation, latex({#1}\wedge_{\scriptstyle\it Bool}{#2}), hook(#BOOL:_andBool_)]
                | K "andThenBool" K       [function, left, smtlib(and), boolOperation, hook(#BOOL:_andThenBool_)]
                > Bool "xorBool" Bool     [function, left, smtlib(xor), boolOperation, hook(#BOOL:_xorBool_)]
                > Bool "orBool" Bool      [function, left, smtlib(or), boolOperation, latex({#1}\vee_{\scriptstyle\it Bool}{#2}), hook(#BOOL:_orBool_)]
                | K "orElseBool" K        [function, left, smtlib(or), boolOperation, hook(#BOOL:_orElseBool_)]
                > Bool "impliesBool" Bool [function, left, smtlib(=>), boolOperation, hook(#BOOL:_impliesBool_)]
                > left:
                  Bool "==Bool" Bool      [function, left, smtlib(=), hook(#BOOL:_==Bool_)]
                | Bool "=/=Bool" Bool     [function, left, smtlib(distinct), hook(#BOOL:_=/=Bool_)]

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
  syntax Int [hook(#INT)]
  syntax Int ::= r"[\\+-]?[0-9]+" [prefer, token]
endmodule

module INT
  imports INT-SYNTAX
  imports BOOL
  imports K-EQUAL

  syntax Int ::= "~Int" Int                     [function, latex(\mathop{\sim_{\scriptstyle\it Int}}{#1}), hook(#INT:~Int_)]
               > left:
                 Int "^Int" Int                 [function, left, latex({#1}\mathrel{{\char`\^}_{\!\scriptstyle\it Int}}{#2}), hook(#INT:_^Int_)]
               > left:
                 Int "*Int" Int                 [function, left, smtlib(*), latex({#1}\mathrel{\ast_{\scriptstyle\it Int}}{#2}), hook(#INT:_*Int_)]
               /* FIXME: translate /Int and %Int into smtlib */
               /* /Int and %Int implement t-division */
               | Int "/Int" Int                 [function, left, smtlib(div), latex({#1}\mathrel{\div_{\scriptstyle\it Int}}{#2}), hook(#INT:_/Int_)]
               | Int "%Int" Int                 [function, left, smtlib(mod), latex({#1}\mathrel{\%_{\scriptstyle\it Int}}{#2}), hook(#INT:_%Int_)]
               /* divInt and modInt implement e-division */
               | Int "divInt" Int               [function, left, smtlib(div)]
               | Int "modInt" Int               [function, left, smtlib(mod), hook(#INT:_modInt_)]
               > left:
                 Int "+Int" Int                 [function, left, smtlib(+), latex({#1}\mathrel{+_{\scriptstyle\it Int}}{#2}), hook(#INT:_+Int_)]
               | Int "-Int" Int                 [function, left, smtlib(-), latex({#1}\mathrel{-_{\scriptstyle\it Int}}{#2}), hook(#INT:_-Int_)]
               > left:
                 Int ">>Int" Int                [function, left, latex({#1}\mathrel{\gg_{\scriptstyle\it Int}}{#2}), hook(#INT:_>>Int_)]
               | Int "<<Int" Int                [function, left, latex({#1}\mathrel{\ll_{\scriptstyle\it Int}}{#2}), hook(#INT:_<<Int_)]
               > left:
                 Int "&Int" Int                 [function, left, latex({#1}\mathrel{\&_{\scriptstyle\it Int}}{#2}), hook(#INT:_&Int_)]
               > left:
                 Int "xorInt" Int               [function, left, latex({#1}\mathrel{\oplus_{\scriptstyle\it Int}}{#2}), hook(#INT:_xorInt_)]
               > left:
                 Int "|Int" Int                 [function, left, latex({#1}\mathrel{|_{\scriptstyle\it Int}}{#2}), hook(#INT:_|Int_)]
  syntax Int ::= "minInt" "(" Int "," Int ")"   [function, smtlib(int_min), hook(#INT:minInt)]
               | "maxInt" "(" Int "," Int ")"   [function, smtlib(int_max), hook(#INT:maxInt)]
               | "absInt" "(" Int ")"           [function, smtlib(int_abs), klabel(absInt), hook(#INT:absInt)]

  rule I1:Int divInt I2:Int => `I1 -Int `I1 modInt I2`` /Int I2
  requires I2 =/=Int 0
  rule
    I1:Int modInt I2:Int
  =>
    ``I1 %Int absInt(I2)` +Int absInt(I2)` %Int absInt(I2)
  requires I2 =/=Int 0

  syntax Bool ::= Int "<=Int" Int         [function, left, smtlib(<=), latex({#1}\mathrel{\leq_{\scriptstyle\it Int}}{#2}), hook(#INT:_<=Int_)]
                | Int "<Int" Int          [function, left, smtlib(<), latex({#1}\mathrel{<_{\scriptstyle\it Int}}{#2}), hook(#INT:_<Int_)]
                | Int ">=Int" Int         [function, left, smtlib(>=), latex({#1}\mathrel{\geq_{\scriptstyle\it Int}}{#2}), hook(#INT:_>=Int_)]
                | Int ">Int" Int          [function, left, smtlib(>), latex({#1}\mathrel{>_{\scriptstyle\it Int}}{#2}), hook(#INT:_>Int_)]
                | Int "==Int" Int         [function, left, smtlib(=), latex({#1}\mathrel{{=}{=}_{\scriptstyle\it Int}}{#2}), hook(#INT:_==Int_)]
                | Int "=/=Int" Int        [function, left, smtlib(distinct), latex({#1}\mathrel{{=}{/}{=}_{\scriptstyle\it Int}}{#2}), hook(#INT:_=/=Int_)]
                | Int "dividesInt" Int    [function]

  rule I1:Int ==Int I2:Int => I1 ==K I2
  rule I1:Int =/=Int I2:Int => notBool `I1 ==Int I2`
  rule `I1:Int dividesInt I2:Int` => `I2 %Int I1` ==Int 0

  syntax Int ::= freshInt(Int)    [freshGenerator, function]
  rule freshInt(I:Int) => I
endmodule

module FLOAT-SYNTAX
  syntax Float [hook(#FLOAT)]
  syntax Float ::= r"([\\+-]?[0-9]+(\\.[0-9]*)?|\\.[0-9]+)([eE][\\+-]?([0-9]+(\\.[0-9]*)?|\\.[0-9]d+))?([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token]
  syntax Float ::= r"[\\+-]?Infinity([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token]
  syntax Float ::= r"NaN([fFdD]|([pP][0-9]+[xX][0-9]+))?" [token]
endmodule

module FLOAT
  imports FLOAT-SYNTAX
  imports BOOL
  imports INT-SYNTAX

  syntax Int ::= precisionFloat(Float) [function, hook(#FLOAT:precision)]
               | exponentFloat(Float) [function, hook(#FLOAT:exponent)]
               | exponentBitsFloat(Float) [function, hook(#FLOAT:exponentBits)]

  syntax Bool ::= signFloat(Float)      [function, hook(#FLOAT:sign)]
                | isNaN(Float)          [function, smtlib((not (== #1 #1))), hook(#FLOAT:isNaN)]
                | isInfinite(Float)     [function]
  syntax MInt ::= significandFloat(Float) [function, hook(#FLOAT:significand)]

  syntax Float ::= fpNaN(Int, Int)              [smtlib((as NaN (_ FP #1 #2)))]
                 | plusInfinity(Int, Int)       [smtlib((as plusInfinity (_ FP #1 #2)))]
                 | minusInfinity(Int, Int)      [smtlib((as minusInfinity (_ FP #1 #2)))]

  syntax Float ::= "--Float" Float             [function, smtlib(-), hook(#FLOAT:neg)]
                 > Float "^Float" Float        [function, left, latex({#1}^{#2}), hook(#FLOAT:pow)]
                 > left:
                   Float "*Float" Float        [function, left, smtlib((* roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\ast_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:mul)]
                 | Float "/Float" Float        [function, left, smtlib((/ roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\div_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:div)]
                 | Float "%Float" Float        [function, left, smtlib((remainder roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{\%_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:rem)]
                 > left:
                   Float "+Float" Float        [function, left, smtlib((+ roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{+_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:add)]
                 | Float "-Float" Float        [function, left, smtlib((- roundNearestTiesToEven #1 #2)), latex({#1}\mathrel{-_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:sub)]

  syntax Float ::= rootFloat(Float, Int)        [function, hook(#FLOAT:root)]
                 | absFloat(Float)              [function, smtlib(abs), hook(#FLOAT:abs)]
                 | roundFloat(Float, Int, Int)  [function, hook(#FLOAT:round)]
                 | floorFloat(Float)            [function, hook(#FLOAT:floor)]
                 | ceilFloat(Float)             [function, hook(#FLOAT:ceil)]
                 | expFloat(Float)              [function, hook(#FLOAT:exp)]
                 | logFloat(Float)              [function, hook(#FLOAT:log)]
                 | sinFloat(Float)              [function, hook(#FLOAT:sin)]
                 | cosFloat(Float)              [function, hook(#FLOAT:cos)]
                 | tanFloat(Float)              [function, hook(#FLOAT:tan)]
                 | asinFloat(Float)             [function, hook(#FLOAT:asin)]
                 | acosFloat(Float)             [function, hook(#FLOAT:acos)]
                 | atanFloat(Float)             [function, hook(#FLOAT:atan)]
                 | atan2Float(Float, Float)     [function, hook(#FLOAT:atan2)]
                 | maxFloat(Float, Float)       [function, smtlib(max), hook(#FLOAT:max)]
                 | minFloat(Float, Float)       [function, smtlib(min), hook(#FLOAT:min)]
                 | sqrtFloat(Float)             [function]
                 | maxValueFloat(Int, Int)      [function, hook(#FLOAT:maxValue)]
                 | minValueFloat(Int, Int)      [function, hook(#FLOAT:minValue)]

  syntax Bool ::= Float "<=Float" Float       [function, left, smtlib(<=), latex({#1}\mathrel{\leq_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:le)]
                | Float "<Float" Float        [function, left, smtlib(<), latex({#1}\mathrel{<_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:lt)]
                | Float ">=Float" Float       [function, left, smtlib(>=), latex({#1}\mathrel{\geq_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:ge)]
                | Float ">Float" Float        [function, left, smtlib(>), latex({#1}\mathrel{>_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:gt)]
                | Float "==Float" Float       [function, left, smtlib(==), latex({#1}\mathrel{==_{\scriptstyle\it Float}}{#2}), hook(#FLOAT:eq)]
                | Float "=/=Float" Float      [function, left, smtlib((not (== #1 #2))), latex({#1}\mathrel{\neq_{\scriptstyle\it Float}}{#2})]


  rule F1:Float =/=Float F2:Float => notBool `F1 ==Float F2`

  syntax Float ::= Int2Float(Int, Int, Int)    [function, klabel(Int2Float), latex({\\it{}Int2Float}), hook(#CONVERSION:int2Float)]
  syntax Int ::= Float2Int(Float)    [function, klabel(Float2Int), latex({\\it{}Float2Int}), hook(#CONVERSION:float2Int)]

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
  syntax String [hook(#STRING)]
  syntax String ::= r"[\\\"](([^\\\"\n\r\\\\])|([\\\\][nrtf\\\"\\\\])|([\\\\][x][0-9a-fA-F]{2})|([\\\\][u][0-9a-fA-F]{4})|([\\\\][u][0-9a-fA-F]{8}))*[\\\"]"      [token, hook(org.kframework.kore.KString)]
endmodule

module STRING
  imports STRING-SYNTAX
  imports INT
  imports FLOAT-SYNTAX
  imports K-EQUAL

  syntax String ::= String "+String" String    [function, left, latex({#1}+_{\scriptstyle\it String}{#2}), hook(#STRING:_+String_)]

  syntax Bool ::= String "==String" String [function, left, hook(#STRING:_==String_)]

  syntax Int ::= "lengthString" "(" String ")" [function, klabel(lengthString), hook(#STRING:lengthString)]
  syntax String ::= "chrChar" "(" Int ")"      [function, klabel(chrChar), hook(#STRING:chrChar)]
  syntax Int ::= "ordChar" "(" String ")"      [function, klabel(ordChar), hook(#STRING:ordChar)]

  syntax String ::= "substrString" "(" String "," Int "," Int ")" [function, klabel(substrString), hook(#STRING:substrString)]
  syntax Int ::= "findString" "(" String "," String "," Int ")"   [function, klabel(findString), hook(#STRING:findString)]
  syntax Int ::= "rfindString" "(" String "," String "," Int ")"  [function, klabel(rfindString), hook(#STRING:rfindString)]
  syntax Int ::= "findChar" "(" String "," String "," Int ")"     [function, klabel(findChar), hook(#STRING:findChar)]
  syntax Int ::= "rfindChar" "(" String "," String "," Int ")"    [function, klabel(rfindChar), hook(#STRING:rfindChar)]

  syntax String ::= "Float2String" "(" Float ")"            [function, klabel(Float2String), hook(#CONVERSION:float2string)]
  syntax String ::= "Float2String" "(" Float "," String ")" [function, klabel(FloatFormat), hook(#CONVERSION:floatFormat)]
  syntax Float  ::= "String2Float" "(" String ")"           [function, klabel(String2Float), hook(#CONVERSION:string2float)]
  syntax Int    ::= "String2Int"   "(" String ")"           [function, klabel(String2Int), hook(#CONVERSION:string2int)]
  syntax String ::= "Int2String"   "(" Int ")"              [function, klabel(Int2String), hook(#CONVERSION:int2string)]
  syntax String ::= "Base2String"  "(" Int "," Int ")"      [function, klabel(Base2String), hook(#CONVERSION:base2string)]
  syntax Int    ::= "String2Base"  "(" String "," Int ")"   [function, klabel(String2Base), hook(#CONVERSION:string2base)]


  syntax String ::= "replaceAll" "(" String "," String "," String ")"      [function, hook(#STRING:replaceAll)]
  syntax String ::= "replace" "(" String "," String "," String "," Int ")" [function, hook(#STRING:replace)]
  syntax String ::= "replaceFirst" "(" String "," String "," String ")"    [function, hook(#STRING:replaceFirst)]
  syntax Int ::= "countAllOccurences" "(" String "," String ")"            [function, hook(#STRING:countAllOccurences)]

  syntax Bool ::= String "=/=String" String      [function, left, hook(#STRING:_=/=String_)]
  rule S1:String =/=String S2:String => notBool `S1 ==String S2`
  rule S1:String ==String S2:String => S1 ==K S2

  syntax Bool ::= String  "<String" String [function, hook(#STRING:_<String_)]
                | String "<=String" String [function, hook(#STRING:_<=String_)]
                | String  ">String" String [function, hook(#STRING:_>String_)]
                | String ">=String" String [function, hook(#STRING:_>=String_)]

  syntax String ::= categoryChar(String)       [function, hook(#STRING:categoryChar)]
                  | directionalityChar(String) [function, hook(#STRING:directionalityChar)]

  rule S1:String <=String S2:String => notBool `S2 <String S1`
  rule S1:String >String S2:String => S2 <String S1
  rule S1:String >=String S2:String => notBool `S1 <String S2`

  rule findChar(S1:String, S2:String, I:Int) => #if findString(S1, substrString(S2, 0, 1), I) ==Int -1 #then findChar(S1, substrString(S2, 1, lengthString(S2)), I) #else #if findChar(S1, substrString(S2, 1, lengthString(S2)), I) ==Int -1 #then findString(S1, substrString(S2, 0, 1), I) #else minInt(findString(S1, substrString(S2, 0, 1), I), findChar(S1, substrString(S2, 1, lengthString(S2)), I)) #fi #fi requires S2 =/=String ""
  rule findChar(_, "", _) => -1
  rule rfindChar(S1:String, S2:String, I:Int) => maxInt(rfindString(S1, substrString(S2, 0, 1), I), rfindChar(S1, substrString(S2, 1, lengthString(S2)), I)) requires S2 =/=String ""
  rule rfindChar(_, "", _) => -1

  rule countAllOccurences(Source:String, ToCount:String) => 0
            requires findString(Source, ToCount, 0) <Int 0
  rule countAllOccurences(Source:String, ToCount:String) => 1 +Int countAllOccurences(substrString(Source, findString(Source, ToCount, 0) +Int lengthString(ToCount), lengthString(Source)), ToCount)
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
  rule replaceAll(Source:String, ToReplace:String, Replacement:String) => replace(Source, ToReplace, Replacement, countAllOccurences(Source, ToReplace))

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
                    K "==K" K           [function, smtlib(=), hook(#K-EQUAL:_==K_), latex({#1}\mathrel{=_K}{#2}), equalEqualK]
                | K "=/=K" K          [function, smtlib(distinct), hook(#K-EQUAL:_=/=K_), latex({#1}\mathrel{\neq_K}{#2}), notEqualEqualK]

  syntax priorities equalEqualK notEqualEqualK > boolOperation
  rule K1:K =/=K K2:K => notBool `K1 ==K K2`

  rule K1:Bool ==Bool K2:Bool => K1 ==K K2

  syntax K ::= "#if" Bool "#then" K "#else" K "#fi"   [function, hook(KEqual:ite)]
  rule #if true #then K:K #else _:K #fi => K
  rule #if false #then _:K #else K:K #fi => K

endmodule

module K-REFLECTION
  imports KAST
  imports STRING

  syntax K ::= "#configuration" [function, impure, hook(MetaK:#configuration)]
  syntax String ::= #sort(K) [function, hook(MetaK:#sort)]
  syntax KItem ::= #fresh(String)   [function, hook(#FRESH:fresh), impure]

endmodule

module K-IO
  imports LIST
  imports STRING

  syntax IOError ::= "#EOF" | "#noparse" | "#ENOENT" | "#ENOTDIR" | "#EACCES" | "#ELOOP" | "#ENAMETOOLONG" | "#EBADF" | "#ESPIPE" | "#EISDIR" | "#EINVAL"

  syntax Int ::= "#open" "(" String ")" [function]
               | "#open" "(" String "," String ")" [function, hook(#IO:#open), impure]
               | "#tell" "(" Int ")" [function, hook(#IO:#tell), impure]
               | "#getc" "(" Int ")"             [function, hook(#IO:#getc), impure]
  syntax String ::= "#read" "(" Int "," Int ")"    [function, hook(#IO:#read), impure]

  syntax K ::= "#close" "(" Int ")" [function, hook(#IO:#close), impure]
             | "#seek" "(" Int "," Int ")" [function, hook(#IO:#seek), impure]
             | "#putc" "(" Int "," Int ")"      [function, hook(#IO:#putc), impure]
             | "#write" "(" Int "," String ")" [function, hook(#IO:#write), impure]

  syntax KItem ::= "#stat" "(" String ")" [function, hook(#IO:#stat), impure]
                 | "#lstat" "(" String ")" [function, hook(#IO:#lstat), impure]
                 | "#opendir" "(" String ")" [function, hook(#IO:#opendir), impure]

  syntax KItem ::= "#parse" "(" String "," String ")" [function, klabel(#parse), hook(#K-PARSER:#parse), impure]
  syntax KItem ::= #parseInModule(String, // input
                                  String, // start symbol
                                  String) // module name
                                  [function, hook(#K-PARSER:#parseInModule), impure]

  rule #open(S:String) => #open(S:String, "rw")

  syntax Int ::= "#stdin"   [function]
                | "#stdout" [function]
                | "#stderr" [function]

  syntax Stream ::= #parseInput(String, String)
  syntax Stream ::= #buffer(K)
  syntax Stream ::= #istream(Int)
                  | #ostream(Int)
  syntax Stream ::= "#noIO"

  //TODO(dwightguth): add back support for stream cells
/*
  rule ListItem(#ostream(_))
       ListItem(#buffer(Buffer:String => Buffer +String Float2String(F)))
       `ListItem(F:Float) => .List`
       _:List [stdout, stderr]
  rule ListItem(#ostream(_))
       ListItem(#buffer(Buffer:String => Buffer +String Int2String(I)))
       `ListItem(I:Int) => .List`
       _:List [stdout, stderr]
  rule ListItem(#ostream(_))
       ListItem(#buffer(Buffer:String => Buffer +String S))
       `ListItem(S:String) => .List`
       _:List [stdout, stderr]

  rule ListItem(#buffer(Buffer:String => Buffer +String Float2String(F)))
       `ListItem(F:Float) => .List`
       _:List [stdout, stderr]
  rule ListItem(#buffer(Buffer:String => Buffer +String Int2String(I)))
       `ListItem(I:Int) => .List`
       _:List [stdout, stderr]
  rule ListItem(#buffer(Buffer:String => Buffer +String S))
       `ListItem(S:String) => .List`
       _:List [stdout, stderr]


  // Send first char from the buffer to the server
  rule ListItem(#ostream(`.K => #write(N, S)` ~> N:Int))
       ListItem(#buffer(S:String => ""))
       _:List
    requires S =/=String "" [stdout, stderr]

  // read one character at a time until we read whitespace
  rule ListItem(#parseInput(_:String, Delimiters:String))
       ListItem(#buffer(S:String => S +String chrChar(#getc(N))))
       ListItem(#istream(N:Int))
    requires findChar(S, Delimiters, 0) ==Int -1 [stdin]

  // when we reach whitespace, if it parses create a ListItem
  rule `ListItem(#parseInput("String", Delimiters:String)) => ListItem(S)`
       ListItem(#buffer(S:String => ""))
       _:List
    requires findChar(S, Delimiters, 0) =/=Int -1 [stdin]

  // a hack: handle the case when we read integers without the help of the IO server
  rule `ListItem(#parseInput("Int", Delimiters:String))
       => ListItem(String2Int(substrString(S, 0, findChar(S, Delimiters, 0))))`
       ListItem(#buffer(S:String => substrString(S,findChar(S, Delimiters, 0) +Int 1, lengthString(S))))
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool lengthString(S) >Int 1 [stdin]

  rule `ListItem(#parseInput(Sort:String, Delimiters:String))
       => ListItem(#parse(substrString(S, 0, findChar(S, Delimiters, 0)), Sort))`
       ListItem(#buffer(S:String => substrString(S,findChar(S, Delimiters, 0) +Int 1, lengthString(S))))
       _:List
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool Sort =/=String "String"
       andBool lengthString(S) >Int 1 [stdin]

  rule ListItem(#parseInput(Sort:String, Delimiters:String))
       ListItem(#buffer(S:String => substrString(S, 1, lengthString(S))))
       _:List
    requires findChar(S, Delimiters, 0) =/=Int -1
       andBool Sort =/=String "String"
       andBool lengthString(S) <=Int 1 [stdin]

  rule ListItem(#buffer(_))
       `ListItem(#noIO) ListItem(#istream(_:Int)) => .List` [stdin]

  rule `ListItem(#ostream(_:Int)) ListItem(#noIO) => .List`
       ListItem(#buffer(_))
       _:List [stdout, stderr]
*/
  rule #stdin => 0
  rule #stdout => 1
  rule #stderr => 2

// ------------------------------
// System

  syntax KItem ::= "#system" "(" String ")" [function, klabel(#system), hook(#IO:#system), impure]
                 | "#systemResult" "(" Int /* exit code */ "," String /* stdout */ "," String /* stderr */ ")"

endmodule
