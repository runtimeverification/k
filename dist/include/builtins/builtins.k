require "bool.k"
require "bool-symbolic.k"
require "int.k"
require "int-symbolic.k"
require "float.k"
require "string.k"
require "tcp.k"
require "k-equal.k"
require "random.k"
require "model-checker.k"

module BUILTIN-SYNTAX-HOOKS
  imports BOOL-SYNTAX-HOOKS 
  imports INT-SYNTAX-HOOKS 
  imports FLOAT-SYNTAX-HOOKS 
  imports STRING-SYNTAX-HOOKS
  imports ID-SYNTAX-HOOKS
  imports LTL-SYNTAX-HOOKS
  imports MODEL-CHECKER-SYNTAX-HOOKS
endmodule

module BUILTIN-HOOKS
  imports BOOL-HOOKS 
  imports INT-HOOKS 
  imports FLOAT-HOOKS 
  imports STRING-HOOKS
  imports TCP-HOOKS
  imports K-EQUAL-HOOKS
  imports RANDOM-HOOKS
  imports LTL-HOOKS
  imports MODEL-CHECKER-HOOKS
endmodule

