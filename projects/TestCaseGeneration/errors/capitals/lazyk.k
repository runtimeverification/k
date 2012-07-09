// error with use of capital letter in token of syntax definition

// Parse error: Syntax error near unexpected character ':'
//  	 at: (32,14,32,14) in file: /home/kirarinsnow/k-framework/trunk/dist/
// include/builtins/int.k



module LAZYK-SYNTAX
   syntax Program  ::= CCExpr

   syntax CCExpr   ::= CCExpr Expr
                     | Expr
		   
   syntax Expr     ::= "i"
                     | ExprPrime
 
//  syntax IotaExpr ::= "i"
//                    | ExprPrime

   syntax ExprPrime   ::= "I"               // <- capital letter causes an error
//                     | "K" | "k"
//                     | "S" | "s"
//                     | NonemptyJotExpr
//                     | ">" Expr Expr
//                     | "*" IotaExpr IotaExpr
//                     | "(" CCExpr ")"


//   syntax NonemptyJotExpr ::= NonemptyJotExpr "0"
//                            | NonemptyJotExpr "1"
//                            | "0"
//                            | "1"

      
endmodule

module LAZYK
  imports LAZYK-SYNTAX
  configuration <k> $PGM:Program </k>
  syntax KResult ::= Program
endmodule
