// Copyright (c) 2020 K Team. All Rights Reserved.
module PROOFSYNTAX-SYNTAX
  syntax S ::= "a" | "b"
endmodule

module PROOFSYNTAX
  imports PROOFSYNTAX-SYNTAX
  imports BOOL

  syntax S::= "c" | "d"

  rule a => b [label(A2B)]

  rule b => c [label(B2C)]

  rule c => d [label(C2D)]
endmodule
