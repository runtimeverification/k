// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
  imports BOOL
  imports INT

  syntax Foo ::= foo(Int) | bar() | baz()

  rule foo(I) => bar() requires I  >Int 0 [priority(40)]
  rule foo(I) => baz() requires I >=Int 0 [priority(60)]
endmodule
