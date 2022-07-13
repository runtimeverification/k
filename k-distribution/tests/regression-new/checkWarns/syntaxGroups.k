module SYNTAXGROUPS-SYNTAX
  syntax Exp  ::= Exp "*" Exp [times, unused]
                > Exp "+" Exp [plus,  unused]

  syntax left times plus
endmodule

module SYNTAXGROUPS
  imports SYNTAXGROUPS-SYNTAX
endmodule
