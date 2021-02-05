module CHECKBRACKETFINE-SYNTAX
  syntax Exp ::= "(" Exp [bracket]
  syntax Exp ::= Exp ")" [bracket]
  syntax Exp ::= "(" ")" Exp [bracket]
  syntax Exp ::= "$" Exp [bracket]
  syntax Exp ::= "%*()&@$)" Exp [bracket]
  syntax Exp ::= "OQNFO" "LDKKSFH" Exp "()&*^Y" "\"LKSDH'" [bracket]
  syntax {A} A ::= "(" A ")" [bracket]
  syntax Exp ::= "(" Exp ")" [bracket]
endmodule

module CHECKBRACKETFINE
  imports CHECKBRACKETFINE-SYNTAX

endmodule
