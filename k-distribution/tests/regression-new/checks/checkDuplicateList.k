// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module CHECKDUPLICATELIST-SYNTAX
  imports INT-SYNTAX
  syntax MyList ::= List{Int,""}
endmodule

module CHECKDUPLICATELIST
  imports CHECKDUPLICATELIST-SYNTAX
  syntax MyList ::= List{Int,""}
endmodule
