module ID-SYNTAX-HOOKS
  imports #ID-INTERFACE
  syntax Id ::= #Id 
endmodule

module ID-HOOKS
  imports ID-SYNTAX-HOOKS
  imports K

  syntax Variable ::= Id
endmodule
