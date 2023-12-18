// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module PARAMAMB

  syntax T ::= "wrap" M | "wrap" X
  syntax A
  syntax B
  syntax M ::= A | B
  syntax N ::= A | B | X
  syntax X
  syntax KItem ::= label(N, T)

  rule X => label(X, wrap X)

endmodule
