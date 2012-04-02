require ex.maude

module ISSUE imports #EX

  syntax #S2 ::= "f" "(" Map ")" 

  syntax #S1 ::= "g" "(" Map ")" 

  rule f(g(M:Map)) => f(M) [structural] 

//  macro f(g(M:Map)) = f(M)

end module

