module ID-SYNTAX-HOOKS
  imports #ID-INTERFACE + K
  syntax Id ::= #Id 
endmodule

module ID-HOOKS
  imports ID-SYNTAX-HOOKS
  imports K
endmodule
