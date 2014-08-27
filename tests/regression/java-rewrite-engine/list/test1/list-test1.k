// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/list.k"

module LIST-TEST1
  imports LIST
  configuration <T> <k> $PGM:K </k> <out> .List </out> </T>
  syntax KItem ::= start(Int)

  rule <k> start(I:Int => I:Int -Int 1) ...</k>
       <out>... .List => ListItem(I:Int) </out>
    when I >Int 0
  rule start(0) => .
endmodule
