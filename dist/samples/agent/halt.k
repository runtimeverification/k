require "val.k"
module HALT-SYNTAX
  syntax Exp ::= "halt" Exp [strict]
endmodule

module HALT
  imports HALT-SYNTAX
  imports VAL
  rule <k>(halt V:Val)~>_ => V</k> 
endmodule
