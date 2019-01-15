// Copyright (c) 2018 K Team. All Rights Reserved.
require "domains.k"

module MINT-TEST-SYNTAX
  imports LIST
  imports MINT-SYNTAX
  imports MINT

  syntax KItem ::= MInt
  syntax KItem ::= Bool
  syntax Assert ::= "assert" Bool
  syntax Asserts ::= List{Assert,";"}
  syntax Program ::= Asserts ";"
endmodule

module MINT-TEST
  imports MINT-TEST-SYNTAX

  configuration <k> $PGM:Program </k>

  rule assert true ; As:Asserts => As
  rule As:Asserts ; => As
  rule .Asserts => .K
endmodule
