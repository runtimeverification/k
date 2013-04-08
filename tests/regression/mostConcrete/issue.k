/**
K should find the most concrete common term.
*/
module ISSUE

 syntax Exp ::= Int
 syntax Exp ::= test(Int, Int)  [klabel('correct)]
              | test(Int, Exp)
              | test(Exp, Int)
			  | test(Exp, Exp)
			  | test(K, K)
 
 syntax Val ::= Int | Id
 syntax Exp ::= Val
 syntax Stmt ::= Val
 
 syntax Exp ::= test2(Int)
              | test2(Id)
			  | test2(Val) [klabel('correct2)]
			  | test2(Exp)
			  | test2(Stmt)
 
  configuration
    <k> 'correct( 1,, 2) ~> 'correct2(.) </k>
    <out stream="stdout"> .List </out>

 rule <k> test( 1, 2) => . ...</k>
      <out>... . => ListItem("Correct") </out>

 rule <k> test2( X ) => . ...</k>
      <out>... . => ListItem("Correct2") </out>

endmodule
