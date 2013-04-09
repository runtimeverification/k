/**
K should find the most concrete common term.
*/
module ISSUE

 syntax Ints ::= List{Int,","}
 syntax Exp  ::= Ints
 syntax Stmt ::= Ints
 syntax Exp ::= test(Ints)
			  | test(Exp)
			  | test(Stmt)

 configuration
    <k> test(1) </k>
    <out stream="stdout"> .List </out>

 rule <k> test(X:Int, .Ints) => . ...</k>
      <out>... . => ListItem("Correct") </out>

endmodule
