// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "domains.k"

module A
  imports INT

  configuration <T>
    <k> $PGM:Cmd </k>
  </T>

  syntax Cmd ::= foo( Arg )
               | bar( Arg )
               | "baz"
  syntax Arg ::= arg1 ( Int ) | arg2 ( Int )

  rule <k> foo(X) => bar(X) ... </k>

  syntax Bool ::= isArg1    ( Arg )     [function]
                | isNotArg1 ( Arg )     [function]

  rule isArg1(X)    => arg1(_) :=K  X
  rule isNotArg1(X) => arg1(_) :/=K X

endmodule
