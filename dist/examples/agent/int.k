require "val.k"
module INT-EXP-SYNTAX
  syntax Exp ::= Int
endmodule

module INT-EXP 
  imports VAL
  syntax Val ::= Int 
endmodule
