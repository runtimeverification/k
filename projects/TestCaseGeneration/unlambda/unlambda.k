// Implementation of Unlambda (version 2) in K
// Language specification: http://www.madore.org/~david/programs/unlambda/


// This is a specification for a modified Unlambda syntax, produced by the
// accompanying lexer (lexer.sed).



module UNLAMBDA-SYNTAX
   syntax Fun ::= Atom         // atomic function
              |   ">" Fun Fun  // apply function to function

   syntax Atom ::= "k"         // "constant generator"
               |   "s"         // "substitution"
               |   "i"         // "identity"
               |   "v"         // "void"
               |   "c"         // "call with current continuation"
               |   "d"         // "delay"
               |   "." Int [strict]     // "print"
               |   "r"         // "carriage return"
               |   "e"         // "exit"
               |   "@"         // "read"
               |   "?" Int [strict]    // "compare character read"
               |   "|"         // "reprint character read"
      
endmodule

module UNLAMBDA
  imports UNLAMBDA-SYNTAX
  configuration <k> $PGM:Fun </k>
  syntax KResult ::= Fun

  // reduction rules
  rule > i X:Fun => X [anywhere]

  rule > > k X:Fun Y:Fun => X [anywhere]

  rule > > > s X:Fun Y:Fun Z:Fun => > > X Z > Y Z [anywhere]

  rule > v X:Fun => v [anywhere]

endmodule
