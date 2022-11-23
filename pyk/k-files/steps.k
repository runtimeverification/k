module STEPS-SYNTAX
endmodule

module STEPS
  imports INT
  syntax Foo ::= foo(Int) | bar()
  rule foo(I) => foo(I -Int 1) requires I >Int 0
  rule foo(_) => bar() [owise]
endmodule
