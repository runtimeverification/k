module ANYWHERESIMPLIFICATION

  syntax Foo  ::= a() | b()

  rule a() => b() [anywhere, simplification]

endmodule
