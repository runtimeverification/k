module SYNTAXGROUPS-SYNTAX
  syntax Exp  ::= foo()
                > Exp "*" Exp [times]
                > Exp "+" Exp [plus]

  syntax left times plus
endmodule

module SYNTAXGROUPS
  imports SYNTAXGROUPS-SYNTAX
endmodule
