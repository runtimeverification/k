// Copyright (c) K Team. All Rights Reserved.
module TEST

  syntax KItem ::= "a" | "b" | "c" | "d" | "e"

  rule a => b
  rule a => c
  rule b => d
  rule d => e
  rule d => e
  rule d => e
  rule d => e

endmodule
