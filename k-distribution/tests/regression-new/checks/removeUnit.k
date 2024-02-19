// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module REMOVEUNIT
  imports INT

  syntax Foo [hook(LIST.List)]

  syntax Foo ::= Foo Foo        [left, function, total, hook(LIST.concat), klabel(_Foo_), unit(.Foo), element(FooItem)]
               | ".Foo"         [function, total, hook(LIST.unit), klabel(.Foo), symbol]
               | FooItem(KItem) [function, total, hook(LIST.element), klabel(FooItem), symbol]

  rule X:Int => FooItem(X) .Foo

endmodule
