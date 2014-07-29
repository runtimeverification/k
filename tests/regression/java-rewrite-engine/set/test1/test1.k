// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/set.k"

module TEST1
  imports SET

  syntax KItem ::= start(Int)

  configuration <T> <k> $PGM:K </k> <set> .Set </set> </T>

  rule <k> start(I:Int => I -Int 1) ...</k> <set>... .Set => SetItem(I) ...</set>
    when I >Int 0
  rule start(0) => .
endmodule

