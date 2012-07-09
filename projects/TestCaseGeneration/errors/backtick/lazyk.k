// error with use of '`' in syntax definition


// Error: Warning: <standard input>, line 487 (mod LAZYK-SYNTAX): skipped: `
// Warning: <standard input>, line 487 (mod LAZYK-SYNTAX): skipped: `



module LAZYK-SYNTAX
   syntax Program  ::= CCExpr

   syntax CCExpr   ::= CCExpr Expr
                     | Expr

   syntax Expr     ::= "im"
                     | ExprPrime
 
//  syntax IotaExpr ::= "i"
//                    | ExprPrime

   syntax ExprPrime ::= "ii"
                      | "k"
                      | "s"
//                     | NonemptyJotExpr
                      | "`" Expr Expr         // <- '`' character not usable
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
