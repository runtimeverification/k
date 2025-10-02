// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKSYMBOLKLABEL
  syntax Foo ::= foo() [symbol(foo)]
               | bar() [symbol(bar), klabel(baz)]
endmodule
