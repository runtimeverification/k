// Copyright (c) 2018-2019 K Team. All Rights Reserved.
module TEST
  imports INT
  imports BOOL
  imports MAP

  syntax Foo ::= foo(Int)

  syntax Foo ::= freshFoo(Int)    [freshGenerator, function, functional]
  rule freshFoo(I:Int) => foo(I)

  syntax KItem ::= foo(Foo, Int, Int, Int)

  rule 0 => foo(!I:Foo, !X:Int, !X:Int, !Y:Int)

  configuration <k> $PGM:K </k> <dummy> 0 </dummy>

endmodule
