// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module LOCALDUPLICATELIST-SYNTAX
endmodule

module LOCALDUPLICATELIST
  imports BOOL-SYNTAX
  imports INT-SYNTAX

  syntax Foo ::= List{Bool, ","}
  syntax Foo ::= List{Int, ";"}
endmodule
