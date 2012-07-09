// bizarre error due to use of "i"
// kompiles successfully after replacing "i" with another lowercase letter ("c")

/*

Warning: Warning! Parsing ambiguity at: (32,2,32,2) in file: /home/kirarinsnow/
k-framework/trunk/dist/include/builtins/int.k
    Ambiguity between: "isNat" "(" Int ")" (Bool133Syn), CCExpr Expr 
(CCExpr1284Syn)    Arbitrarily choosing the first.
Warning: Warning! Parsing ambiguity at: (41,2,41,2) in file: /home/kirarinsnow/
k-framework/trunk/dist/include/builtins/string.k
    Ambiguity between: "isChar" "(" String ")" (Bool165Syn), CCExpr Expr 
(CCExpr1284Syn)    Arbitrarily choosing the first.
Warning: Warning! Parsing ambiguity at: (96,2,96,2) in file: /home/kirarinsnow/
k-framework/trunk/dist/include/modules/uris.k
    Ambiguity between: class ro.uaic.info.fmse.k.Variable, class 
ro.uaic.info.fmse.k.KApp, Map "(" K ")" (K1207Builtin)    Arbitrarily choosing 
the first.
Warning: Warning! Parsing ambiguity at: (100,2,100,2) in file: /home/
kirarinsnow/k-framework/trunk/dist/include/modules/uris.k
    Ambiguity between: "isChar" "(" String ")" (Bool165Syn), CCExpr Expr 
(CCExpr1284Syn)    Arbitrarily choosing the first.
Warning: Warning! Parsing ambiguity at: (135,2,135,2) in file: /home/
kirarinsnow/k-framework/trunk/dist/include/modules/uris.k
    Ambiguity between: "isChar" "(" String ")" (Bool165Syn), CCExpr Expr 
(CCExpr1284Syn)    Arbitrarily choosing the first.
Error: Warning: <standard input>, line 427 (mod URIS): bad token i.
Warning: <standard input>, line 427 (mod URIS): no parse for statement
mb rule _=>_ (#printChar`(_`) (C:K), #fPrintChar`(_`,_`) (#stdout, C:K)) when
    __ (__ (__ (i, s), s), C:K) : KSentence [metadata "anywhere=() location=(
/home/kirarinsnow/k-framework/trunk/dist/include/modules/uris.k:96:2:96:2)"] .

*/





module LAZYK-SYNTAX
   syntax Program  ::= CCExpr

   syntax CCExpr   ::= CCExpr Expr
                     | Expr
		   
   syntax Expr     ::= "j"
                     | ExprPrime
 
//  syntax IotaExpr ::= "i"
//                    | ExprPrime

   syntax ExprPrime   ::= "i"     // <- kompiles when "i" is replaced with "c"
                       | "k"
                       | "s"
//                     | NonemptyJotExpr
                       | ">" Expr Expr
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
