require "builtins/set.k"

module TEST2
  imports SET

  syntax K ::= start(Int)

  configuration
    <T>
      <set> MySetItem(0), MySetItem(1), MySetItem(2), MySetItem(3), MySetItem(4) </set> 
			<k> $PGM:K </k> 
		</T>
  
  rule <k> start(I:Int => I -Int 1) ...</k> 
	     <set>... MySetItem(I) => .MySet ...</set>
    when I >Int 0

  rule start(0) => .
endmodule

