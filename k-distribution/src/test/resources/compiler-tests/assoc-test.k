// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
requires "domains.md"

module ASSOC-TEST
  imports INT
  syntax S ::= S "*" S    [assoc, unit(.S)]
             | ".S"       [dot]
             | "a"
             | "b"

  syntax KItem ::= foo(S)
  rule 0 => foo((b * b) * (b * b))
  rule foo((X * (b => a * a) ) * b)
  rule foo((X * a) * Y) => 1

  configuration <k> $PGM </k>
endmodule
