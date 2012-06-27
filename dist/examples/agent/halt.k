module HALT-SYNTAX
  syntax K ::= "halt" K [strict]
endmodule

module HALT
  imports HALT-SYNTAX
  rule <k>(halt V:KResult)~>_ => V</k> 
endmodule
