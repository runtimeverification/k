module CHECKBRACKET-SYNTAX
  syntax A
  syntax Exp ::= "(" A ")" [bracket]
endmodule

module CHECKBRACKET
  imports CHECKBRACKET-SYNTAX

endmodule
