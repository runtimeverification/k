require rexp

module ISSUE imports #REXP + K
  syntax Var ::= Id
  syntax Alph ::= Var
  syntax Rexp ::= Alph

end module

