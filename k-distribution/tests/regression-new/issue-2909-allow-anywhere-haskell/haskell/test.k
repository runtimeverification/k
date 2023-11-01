// Copyright (c) K Team. All Rights Reserved.
module TEST
  imports INT

  syntax Foo ::= foo() | bar() | baz()

  rule foo() => bar() [anywhere, priority(20)]
  rule foo() => baz()
endmodule
