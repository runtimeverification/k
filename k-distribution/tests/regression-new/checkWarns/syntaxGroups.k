// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module SYNTAXGROUPS-SYNTAX
  syntax Exp  ::= Exp "*" Exp [group(times), unused]
                > Exp "+" Exp [group(plus),  unused]

  syntax left times plus
endmodule

module SYNTAXGROUPS
  imports SYNTAXGROUPS-SYNTAX
endmodule
