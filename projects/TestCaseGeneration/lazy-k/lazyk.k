// Implementation of Lazy K in K
// Language specification: http://homepages.cwi.nl/~tromp/cl/lazy-k.html
// Distribution: http://esoteric.sange.fi/essie2/download/lazy-k/


// This is a specification for a modified Lazy K syntax, produced by the
// accompanying lexer (lexer.sed).


// Note: The Iota syntax of Lazy K is currently not implemented due to
// unresolved conflicts in K.



module LAZYK-SYNTAX
   syntax Program  ::= Write CCExpr

   syntax CCExpr   ::= CCExpr Expr
                     | Expr

   syntax Expr     ::= "!"
                     | ExprPrime
                     | Read
 
//   syntax IotaExpr ::= "!"
//                     | ExprPrime

   syntax ExprPrime  ::= "k"
                       | "s"
                       | "j"
                       | NonemptyJotExpr
                       | "=" Expr Expr
//                       | "*" IotaExpr IotaExpr
                       | "[" CCExpr "]"
                       | "[" "]"


   syntax NonemptyJotExpr ::= NonemptyJotExpr Zero
                            | NonemptyJotExpr One
                            | Zero
                            | One

   syntax Zero ::= "z"  
   syntax One ::= "o"

   syntax Write ::= "write"
   syntax Read ::= "read"

endmodule

module LAZYK
  imports LAZYK-SYNTAX
  configuration
    <k> $PGM:Program </k>
    <streams>
      <in stream="stdin"> $IN:List </in>
      <out stream="stdout"> .List </out>
    </streams>
    syntax KResult ::= Program

  
 //rule  read => s  [anywhere]


 // [anywhere] tag does not match, if <k> ... </k> is used
 rule <k> read => I ...</k> 
       <in> ListItem(I) => . ...</in> [anywhere]


//  rule [Input]:
//    <k> A:In => k ...</k>
//    <in>  => . ...</in>
    
    

//  syntax KLabel ::= firstChar
//  syntax KLabel ::= butFirstChar
//  syntax KLabel ::= charToAscii
	
//  rule [firstChar]:
//    firstChar(str(S:String)(.List{K})) =>
//      str(substrString(S:String, 0, 1))(.List{K})
//      [structural]

  //rule [charToAscii]: 
//    charToAscii(str(C:Char)(.List{K})) => int(asciiString(C:Char))(.List{K})
//      [structural]

/*  rule [butFirstChar]: 
    butFirstChar(str(S:String)(.List{K})) => 
      str(substrString(S:String, 1, lengthString(S:String)))(.List{K})
      [structural]
*/


endmodule
