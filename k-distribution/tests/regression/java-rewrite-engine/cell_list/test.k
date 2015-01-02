// Copyright (c) 2013-2015 K Team. All Rights Reserved.
require "builtins/list.k"

module TEST
  imports MAP

  configuration
    <k> $PGM:K </k>
    <list list="">
      <element multiplicity="*">
        0
      </element>
    </list>


  syntax Op ::= push(Int)
              | "push_back" "(" Int ")"
              | "pop" "(" ")"
              | "pop_back" "(" ")"
              | "front" "(" ")"
              | "back" "(" ")"
              | Op ";" Op [right]

  rule O1 ; O2 => O1 ~> O2
  rule
    <k> push(E) => . ...</k>
    <list> (. => <element> E </element>) ...</list>
  rule
    <k> push_back(E) => . ...</k>
    <list>... (. => <element> E </element>) </list>
  rule
    <k> pop() => . ...</k>
    <list> (<element> _ </element> => .) ...</list>
  rule
    <k> pop_back() => . ...</k>
    <list>... (<element> _ </element> => .) </list>
   rule
    <k> front() => E ...</k>
    <list> <element> E:Int </element> ...</list>
  rule
    <k> back() => E ...</k>
    <list>... <element> E:Int </element> </list>
endmodule

