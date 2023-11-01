// Copyright (c) K Team. All Rights Reserved.
module TEST
  imports K-REFLECTION

  syntax Foo ::= parseFoo() [function]
  rule parseFoo() => #parseKORE("Lblfoo{}()")
  syntax Foo ::= foo() [symbol]
endmodule
