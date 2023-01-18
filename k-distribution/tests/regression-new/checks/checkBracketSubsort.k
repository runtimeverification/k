// Copyright (c) K Team. All Rights Reserved.
module CHECKBRACKETSUBSORT-SYNTAX
  syntax A
  syntax Exp ::= A
  syntax Exp ::= "(" A ")" [bracket]
endmodule

module CHECKBRACKETSUBSORT
  imports CHECKBRACKETSUBSORT-SYNTAX

endmodule
