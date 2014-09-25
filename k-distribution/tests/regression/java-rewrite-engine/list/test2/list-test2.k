// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/list.k"

module LIST-TEST2
  imports LIST
  configuration <T> <k> $PGM:K </k> <in> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </in> </T>
  syntax KItem ::= start(Int)

  rule <k> start(I:Int => I -Int 1) ...</k>
       <in> ListItem(_:KItem) => .List ...</in>
    when I >Int 0
  rule start(0) => .
endmodule
