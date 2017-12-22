module TEST-SYNTAX
  syntax Exp ::= "\\" Id "." Exp
               | Id
endmodule

module TEST
  imports TEST-SYNTAX
endmodule
