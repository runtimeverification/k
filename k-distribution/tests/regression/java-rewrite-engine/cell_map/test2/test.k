// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "builtins/map.k"

/**
  * Scenario: multiplicity cell inside cell map
  * Test: AC-Matching/Unification inside cell map, i.e.,
  * AC-Matching/Unification during the evaluation of
  * side-conditions
  */
module TEST
  imports MAP

  configuration
    <k> $PGM:K </k>
    <map1 map="">
      <entry1 multiplicity="*">
        <key1 key=""> .K </key1>
        <map2>
          <entry2 multiplicity="*">
            <key2> .K </key2>
            <value> .K </value>
          </entry2>
        </map2>
      </entry1>
    </map1>


  syntax Op ::= load(Int, Int)
              | create(Int)
              | store(Int, Int, Int)
              | Op ";" Op [right]

  rule O1 ; O2 => O1 ~> O2

  rule
    <k> load(K1, K2) => V ...</k>
    <key1> K1 </key1>
    <key2> K2 </key2>
    <value> V </value>

  rule
    <k> create(K) => .K ...</k>
    ( . => <entry1>... <key1> K </key1> ...</entry1>)

  rule
    <k> store(K1, K2, V) => .K ...</k>
    <key1> K1 </key1>
    <map2>...
      (. => <entry2>
             <key2> K2 </key2>
             <value> V </value>
           </entry2>)
     ...</map2>
endmodule
