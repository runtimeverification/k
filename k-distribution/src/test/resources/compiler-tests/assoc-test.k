// Copyright (c) 2014-2015 K Team. All Rights Reserved.
require "domains.k"

module ASSOC-TEST
  imports INT
  syntax S ::= S "*" S    [assoc, unit(.S)]
             | ".S"       [dot]
             | "a"
             | "b"

  syntax KItem ::= foo(S)
  rule <k> 0 => foo(`b * b` * `a * b`) </k>
  rule <k> foo(`X * a` * Y) => 1 </k>

  configuration <k> $PGM </k>
endmodule
