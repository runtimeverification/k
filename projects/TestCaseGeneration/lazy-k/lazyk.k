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

   syntax ExprPrime  ::= UnlambdaExpr
                       | NonemptyJotExpr
//                       | "*" IotaExpr IotaExpr
                       | "[" CCExpr "]"
                       | "[" "]"

   syntax UnlambdaExpr ::= "s"
                         | "k"
                         | "j"
                         | ">" Expr Expr

   syntax NonemptyJotExpr ::= NonemptyJotExpr JotDigit [right]
                            | TerminalJot

   syntax TerminalJot ::= JotDigit

   syntax JotDigit ::= Zero | One

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


  
  // CC expressions
  rule [ ] => j [anywhere]
  rule X:CCExpr Y:Expr => > X Y [anywhere]
  rule [ X:UnlambdaExpr ] => X [anywhere]


  // TODO: doesn't work right
  // Jot expressions
//  rule X:TerminalJot => > j X [anywhere]
//  rule X:UnlambdaExpr z => > > X s k [anywhere]
//  rule X:UnlambdaExpr o => 
//       > > s > k > s > k X > > s > > s > k s > > s > k k j > k j [anywhere]


  rule ! => j [anywhere]
  rule > j X:Expr => X [anywhere]

  rule > > k X:Expr Y:Expr => X [anywhere]

  rule > > > s X:Expr Y:Expr Z:Expr => > > X Z > Y Z [anywhere]





  // TODO: Output


 




 // "read" is i (disabled input)
 rule read => j [anywhere]

 // TODO: Input

  //rule  read => s  [anywhere]
 
 //rule <k>... read => C ...</k> 
//       <in> ListItem(C:Char) => . ...</in>


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

//  rule [charToAscii]: 
//    charToAscii(str(C:Char)(.List{K})) => int(asciiString(C:Char))(.List{K})
//      [structural]

//  rule [butFirstChar]: 
//  butFirstChar(str(S:String)(.List{K})) => 
//    str(substrString(S:String, 1, lengthString(S:String)))(.List{K})
//    [structural]



endmodule
