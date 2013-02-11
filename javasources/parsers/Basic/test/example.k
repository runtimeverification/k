// header
module IMP-SYNTAX

  syntax Exp ::= Lexer{[a-zA-Z0-9\0\r\t\n\ ]([a]"b")+}
  syntax Exp ::= Token{[a]*}
  syntax Exp -/- [a].[b]
  syntax "let" -/- [a-zA-Z]

  rule a b c /\d 
  zdfasf

endmodule
