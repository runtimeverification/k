require "builtins/set.k"
require "builtins/map.k"

module TEST1
  imports SET
  imports MAP
  configuration <T> <set> .MySet </set> <k> $PGM:K </k> <store> .MyMap </store> </T>
  syntax K ::= start(Int)
  
//  rule <k> start(I:Int => I -Int 1) ...</k> <store>... .MyMap => I |-> 0 ...</store>
//    when I >Int 0

  rule <k> start(I:Int => I -Int 1) ...</k> <set>... .MySet => MySetItem(I) ...</set>
    when I >Int 0

  rule start(0) => .
endmodule
