// Copyright (c) 2012-2014 K Team. All Rights Reserved.
require "bool.k"


module IF-SYNTAX
  imports BOOL-EXP-SYNTAX
  syntax Exp ::= "if" Exp "then" Exp "else" Exp   [if, strict(1)]
endmodule

module IF
  imports IF-SYNTAX
  imports BOOL-EXP

  rule if true then E else _ => E
  rule if false then _ else E => E
endmodule
