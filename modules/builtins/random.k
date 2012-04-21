require int.k

module RANDOM-HOOKS
  imports INT-HOOKS
  
  syntax Int ::= "randomRandom" "(" Int ")" [function hook(#RANDOM:randomRandom)]
end module
