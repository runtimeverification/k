// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKBRACKETSUPERSORT-SYNTAX
  syntax A
  syntax Exp ::= A
  syntax A ::= "(" Exp ")" [bracket]
endmodule

module CHECKBRACKETSUPERSORT
  imports CHECKBRACKETSUPERSORT-SYNTAX

endmodule
