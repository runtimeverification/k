module FUNCTIONSIMPLIFICATION-SYNTAX
endmodule

module FUNCTIONSIMPLIFICATION
  imports FUNCTIONSIMPLIFICATION-SYNTAX

  syntax Foo  ::= a() | b()

  rule a() => b() [simplification]

endmodule
