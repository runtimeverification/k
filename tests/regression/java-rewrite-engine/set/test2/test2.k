// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "builtins/set.k"

module TEST2
  imports SET

  syntax KItem ::= start(Int)

  configuration
    <T>
            <k> $PGM:K </k>
      <set> SetItem(0) SetItem(1) SetItem(2) SetItem(3) SetItem(4) </set>
        </T>

  rule <k> start(I:Int => I -Int 1) ...</k>
         <set>... SetItem(I) => .Set ...</set>
    when I >Int 0
  rule start(0) => .
endmodule

