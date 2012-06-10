require "autoinclude.k"

module EXAMPLE-SYNTAX

  syntax Bool ::= K "==K" K [cons("Bool1EqSyn")]
  syntax Bool ::= Bool "andBool" Bool [cons("Bool1AndSyn")]
  
  syntax Bool ::= #Bool
  
  syntax BExp ::= Bool
  
  syntax Stmt ::= "if" BExp "then" Stmt "else" Stmt


  configuration <T> 
                  <k> .K </k>
                  <env> .Map </env>
                  <out> .List </out>
                </T>

endmodule




module EXAMPLE
   imports EXAMPLE-SYNTAX


  rule if true then S else _ => S
  //rule A:K andBool B:K ==K true
  //rule <env>... X |-> (_ => I) ...</env>
  //rule 1 ~> 2 ,, 3 ~> 4 ~> 5 ,, 6
  //rule <out> A B C D </out>


endmodule

