// Copyright (c) 2020 K Team. All Rights Reserved.

module CLAIMLOC
  imports BOOL
  syntax S ::= "a" | "b" | "c" | "d"

  rule a => b [label(A2B)]

  rule b => c [label(B2C)]

  rule c => d [label(C2D)]
endmodule
