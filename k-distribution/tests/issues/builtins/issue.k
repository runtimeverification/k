// Copyright (c) 2012-2014 K Team. All Rights Reserved.

module ISSUE-SYNTAX

  syntax StringNew ::= "newString" "(" Id ")"
                     | String


  syntax Bool ::= StringNew "==String" StringNew

endmodule

module ISSUE
  imports ISSUE-SYNTAX

endmodule
