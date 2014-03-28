require "builtins/list.k"

module LIST-TEST2
  imports LIST
  configuration <T> <in> MyListItem(0), MyListItem(1), MyListItem(2), MyListItem(3) </in> <k> $PGM:K </k> </T>
  syntax K ::= start(Int)
  
  rule <k> start(I:Int => I -Int 1) ...</k> 
       <in> MyListItem(_:KItem) => .MyList ...</in>
    when I >Int 0

  rule start(0) => .
endmodule
