kmod NAT-INF is 
  syntax K ::= NatInf | #Bool 
  syntax NatInf ::= #Nat | "infty" [latex "\infty"]
                  | NatInf "+" NatInf 
  syntax K ::= NatInf "<" NatInf 
  
  rule N:#Nat < infty => true [structural]
  rule N1:#Nat < N2:#Nat => N1 <Nat N2 [structural]
  rule N + infty => infty [structural]  
  rule N1:#Nat + N2:#Nat => N1 +Nat N2 [structural]
endkm
