// error arises when commented lines ("<-") are included;
// not sure how to resolve at the moment; the problem is a conflict between
// the Iota and Unlambda syntaxes of Lazy K


/*
Error: Warning: sort declarations for constant ! do not have an unique least 
sort.
Warning: sort declarations for constant ! do not have an unique least sort.
Warning: sort declarations for constant ! do not have an unique least sort.
Warning: sort declarations for constant ! do not have an unique least sort.
Warning: sort declarations for constant ! do not have an unique least sort.
Warning: sort declarations for constant ! do not have an unique least sort.
Warning: sort declarations for constant ! do...
Check /home/kirarinsnow/k-framework/trunk/projects/TestCaseGeneration/errors/
uniquesort/.k/kompile_err.txt to see the complete error
*/


module LAZYK-SYNTAX
   syntax Program  ::= CCExpr

   syntax CCExpr   ::= CCExpr Expr
                     | Expr
		   
   syntax Expr     ::= "!"
                     | ExprPrime
 
   syntax IotaExpr ::= "!"                // <-
                     | ExprPrime          // <-

   syntax ExprPrime  ::= "k"
                       | "s"
                       | "j"
                       | NonemptyJotExpr
                       | ">" Expr Expr
                       | "*" IotaExpr IotaExpr     // <-
                       | "[" CCExpr "]"

   syntax NonemptyJotExpr ::= NonemptyJotExpr "z"
                            | NonemptyJotExpr "o"
                            | "z"
                            | "o"


endmodule

module LAZYK
  imports LAZYK-SYNTAX
  configuration <k> $PGM:Program </k>
  syntax KResult ::= Program
endmodule
