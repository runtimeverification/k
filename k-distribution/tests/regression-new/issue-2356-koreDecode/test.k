module TEST-SYNTAX
  syntax Exps ::= List{Exp,","}

  syntax Exp ::= "#fail" | "?_0" | "_V_9" | "^-_<>&"
endmodule

module TEST
  imports TEST-SYNTAX
  configuration <k> $PGM:Exps </k>
endmodule
