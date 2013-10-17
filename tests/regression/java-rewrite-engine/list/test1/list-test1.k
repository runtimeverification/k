//require "builtins/list.k"

module LIST-TEST1
//  imports LIST
  configuration <T> <out> .List </out> <k> $PGM:K </k> </T>
  syntax K ::= start(Int)
  
//  rule <k> start(I:Int => I -Int 1) ...</k> <store>... .MyMap => I |-> 0 ...</store>
//    when I >Int 0

  rule <k> start(I:Int => I -Int 1) ...</k> 
       <out>... .List => ListItem(I) </out>
    when I >Int 0

  rule start(0) => .
endmodule
