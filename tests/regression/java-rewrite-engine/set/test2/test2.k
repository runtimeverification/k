require "builtins/set.k"
require "builtins/map.k"

module TEST2
  imports SET
  imports MAP
  configuration <T> <set> MySetItem(0) MySetItem(1) MySetItem(2) MySetItem(3)
			  MySetItem(4) </set> 
			<k> $PGM:K </k> 
		</T>
  syntax K ::= start(Int)
  
  rule <k> start(I:Int => I -Int 1) ...</k> 
	<set>... MySetItem(I) => .MySet ...</set>
    when I >Int 0

  rule start(0) => .
endmodule
