// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "builtins/map.k"

module TEST
  imports MAP

  configuration
    <k> $PGM:K </k>
    <map map="">
      <entry multiplicity="*">
        <key key=""> .K </key>
        <value> .K </value>
      </entry>
    </map>


  syntax Op ::= load(Int)
              | store(Int, Int)
              | Op ";" Op [right]

  rule O1 ; O2 => O1 ~> O2
  rule
    <k> load(K) => V ...</k>
    <key> K </key>
    <value> V:Int </value>
  rule
    <k> store(K, V) => .K ...</k>
    <key> K </key>
    <value> _:Int => V </value>
  rule
    <k> store(K, V) => .K ...</k>
    (. => <entry> <key> K </key><value> V </value> </entry>)
endmodule

