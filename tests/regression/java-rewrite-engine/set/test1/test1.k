require "builtins/set.k"

module TEST1
  imports SET

  syntax K ::= start(Int)

  configuration <T> <k> $PGM:K </k> <set> .MySet </set> </T>
  
  rule <k> start(I:Int => I -Int 1) ...</k> <set>... .MySet => MySetItem(I) ...</set>
    when I >Int 0

  rule start(0) => .
endmodule

