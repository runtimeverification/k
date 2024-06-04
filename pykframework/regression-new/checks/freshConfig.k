// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module FRESHCONFIG-SYNTAX
endmodule

module FRESHCONFIG
  imports INT

  syntax Foo ::= foo(Int)

  syntax Foo ::= freshFoo(Int)    [freshGenerator, function, total]
  rule freshFoo(I:Int) => foo(I)

configuration
  <k> $PGM:Int </k>
  <freshFoo> !_:Foo </freshFoo>

  rule 0 => !_:Foo

endmodule
