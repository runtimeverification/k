require "bool.k"
require "int.k"
require "float.k"
require "string.k"
require "tcp.k"
require "k-equal.k"

module BUILTIN-SYNTAX-HOOKS
  imports BOOL-SYNTAX-HOOKS 
  imports INT-SYNTAX-HOOKS 
  imports FLOAT-SYNTAX-HOOKS 
  imports STRING-SYNTAX-HOOKS
  imports ID-SYNTAX-HOOKS
endmodule

module BUILTIN-HOOKS
  imports BOOL-HOOKS 
  imports INT-HOOKS 
  imports FLOAT-HOOKS 
  imports STRING-HOOKS
  imports TCP-HOOKS
  imports K-EQUAL-HOOKS
endmodule
