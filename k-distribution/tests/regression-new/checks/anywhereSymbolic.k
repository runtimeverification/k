module ANYWHERESYMBOLIC

  syntax Foo  ::= a() | b()

  rule a() => b() [anywhere, symbolic]

endmodule
