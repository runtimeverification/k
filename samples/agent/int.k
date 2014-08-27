// Copyright (c) 2013-2014 K Team. All Rights Reserved.
require "val.k"
module INT-EXP-SYNTAX
  syntax Exp ::= Int
endmodule

module INT-EXP
  imports VAL
  syntax Val ::= Int
endmodule
