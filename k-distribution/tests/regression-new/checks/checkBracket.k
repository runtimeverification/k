module CHECKBRACKET-SYNTAX
  syntax {A} A ::= "(" A ")" [bracket]
  syntax Exp ::= "(" Exp ")" [bracket]
  syntax Exp ::= "(" Exp Exp ")" [bracket]
endmodule

module CHECKBRACKET
  imports CHECKBRACKET-SYNTAX

endmodule
