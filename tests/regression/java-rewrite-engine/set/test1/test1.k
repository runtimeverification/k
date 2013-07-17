module TEST1
  configuration <T> <set> .Set </set> <k> start(10) </k> </T>
  syntax K ::= start(Int)
  
  rule <k> start(I:Int => I -Int 1) ...</k> <set>... . => SetItem(I) ...</set>
    when I >Int 0

  rule start(0) => .
endmodule
