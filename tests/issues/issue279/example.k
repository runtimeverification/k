require rexp

module ISSUE is including #REXP + K
  syntax Var ::= #Id
  syntax Alph ::= Var
  syntax Rexp ::= Alph

end module

