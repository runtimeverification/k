// Copyright (c) K Team. All Rights Reserved.
module TEST-SYNTAX
endmodule

module TEST
  imports INT

  syntax Foo ::= foo(Int)

  syntax Foo ::= freshFoo(Int)    [freshGenerator, function, total]
  rule freshFoo(I:Int) => foo(I)

configuration
  <k> $PGM:Int </k>
  <freshFoo> !_:Foo </freshFoo>

  rule 0 => !_:Foo

endmodule
