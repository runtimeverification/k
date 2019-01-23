// Copyright (c) 2018-2019 K Team. All Rights Reserved.

requires "domains.k"

module A

  imports INT

  configuration <T>
    <k> $PGM:Cmd </k>
    <calldata> bytes2(0,0) </calldata>
    <flag> 0 </flag>
  </T>

  // commands

  syntax Cmd ::= call(Int)
               | "run"

  rule <k> call(X) => run ... </k>
       <calldata> _ => split(X) </calldata>

  rule <k> run => merge(CD) ... </k>
       <calldata> CD </calldata>

  // utility functions

  syntax Bytes ::= bytes2(Int, Int)

  syntax Bytes ::= split(Int) [function]

  syntax Int ::= merge(Bytes) [function]

  // abstractions

  syntax Int ::= nth(Int, Int, Int) [function, proj(0,1,2)]

  rule split(X) => bytes2(nth(X,0,2), nth(X,1,2))

  rule merge(bytes2(nth(X,0,2), nth(X,1,2))) => X

endmodule
