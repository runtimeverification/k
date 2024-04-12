// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
  imports INT
  imports BOOL
  imports MAP

  syntax Foo ::= foo(Int)

  syntax Foo ::= freshFoo(Int)    [freshGenerator, function, total]
  rule freshFoo(I:Int) => foo(I)

  syntax KItem ::= foo(Foo, Int, Int, Int)

  rule 0 => foo(!_I:Foo, !X:Int, !X:Int, !_Y:Int)

  configuration <k> $PGM:K </k> <dummy> 0 </dummy>

endmodule
