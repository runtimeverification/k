require /modules/builtins/int
module FLOAT-SYNTAX-HOOKS
  syntax Float ::= #Float
end module

module FLOAT-HOOKS
  imports FLOAT-SYNTAX-HOOKS
  imports K
end module
