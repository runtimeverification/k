// Copyright (c) K Team. All Rights Reserved.
module CHECKBRACKET-SYNTAX
  syntax A
  syntax Exp ::= "(" A ")" [bracket]
endmodule

module CHECKBRACKET
  imports CHECKBRACKET-SYNTAX

endmodule
