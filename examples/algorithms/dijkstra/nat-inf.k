kmod NAT-INF is 
  syntax K ::= #NatInf | #Bool 
  syntax #NatInf ::= #Nat | infty [latex "\infty"]
                  | #NatInf +Nat #NatInf [ditto latex "{#1}\mathrel{\texttt{+}_{\textit{\scriptsize Nat}}}{#2}"]
  syntax #Bool ::= #NatInf <Nat #NatInf [ditto latex "{#1}\mathrel{\texttt{<}_{\textit{\scriptsize Nat}}}{#2}"]
  
  rule N:#Nat <Nat infty => true [structural]
  rule N +Nat infty => infty [structural]  
endkm
