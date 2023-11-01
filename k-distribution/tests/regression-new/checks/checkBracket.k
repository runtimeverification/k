// Copyright (c) K Team. All Rights Reserved.
module CHECKBRACKET-SYNTAX
  syntax Exp ::= "(" Exp Exp ")" [bracket]
endmodule

module CHECKBRACKET
  imports CHECKBRACKET-SYNTAX

endmodule
