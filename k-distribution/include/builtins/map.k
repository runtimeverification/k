// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/list.k"
require "builtins/set.k"


module MAP
  imports LIST
  imports SET

  /*@\section{Description} The Map represents a generalized associative array.
   Each key can be paired with an arbitrary value, and can be used to reference
   its associated value. Multiple bindings for the same key are not allowed. */

  /*@ Construct a new Map consisting of key/value pairs of two Maps (the keys of
   the two Maps are assumed disjoint) */
  syntax Map ::= Map Map                        [left, function, hook(Map:__), klabel('_Map_)]
  /*@  Construct an empty Map */
  syntax Map ::= ".Map"                         [function, hook(Map:.Map)]
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

  /*@ Get a Set consisting of all keys in the Map:*/
  syntax Set ::= keys(Map)                      [function, hook(Map:keys)]

  /*@ Get a List consisting of all values in the Map: */
  syntax List ::= values(Map)                   [function, hook(Map:values)]

  /*@ Get the Map size (number of key/value pairs) */
  syntax Int ::= size(Map)                      [function, hook(Collection:size), klabel('sizeMap)]

  /*@ Check map inclusion */
  syntax Bool ::= Map "<=Map" Map               [function, hook(Map:inclusion)]
endmodule

