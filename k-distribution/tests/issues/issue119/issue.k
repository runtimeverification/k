// Copyright (c) 2013-2015 K Team. All Rights Reserved.
module ISSUE
  syntax A  ::= "a"
  syntax As ::= List{A,","}

  syntax B  ::= As "b" | "(" B ")" [bracket]
  syntax Bs ::= List{B,","}
endmodule

// 1) should report ambiguity when parsing "a, a b"
// 2) should parse "a, (a b)", but it does not
