// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "domains.md"

module A

  imports INT
  imports BOOL
  imports K-REFLECTION

  configuration <T>
    <k> $PGM:Cmd </k>
  </T>

  // commands

  syntax Cmd ::= foo(Int)
               | bar(Int)
               | zoo(Int)

  rule foo(X:Int) => bar(X) requires #isVariable(X)

  rule foo(X:Int) => zoo(X) requires notBool #isVariable(X)

  //

  syntax Int ::= f(Int) [function]

endmodule
