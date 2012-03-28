require bool
require int
require float
require string
require tcp
require k-equal

module BUILTIN-SYNTAX-HOOKS
  imports BOOL-SYNTAX-HOOKS 
  imports INT-SYNTAX-HOOKS 
  imports FLOAT-SYNTAX-HOOKS 
  imports STRING-SYNTAX-HOOKS
  imports ID-SYNTAX-HOOKS
end module

module BUILTIN-HOOKS
  imports BOOL-HOOKS 
  imports INT-HOOKS 
  imports FLOAT-HOOKS 
  imports STRING-HOOKS
  imports TCP-HOOKS
  imports K-EQUAL-HOOKS
end module
