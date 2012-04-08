kmod NAT-INF is 
  syntax K ::= NatInf | Bool 
  syntax NatInf ::= Nat | "infty" [latex "\infty"]


  syntax NatInf ::= NatInf + NatInf   [function]
  syntax Bool ::= NatInf < NatInf     [function]

  
  define N:Nat < infty => true
  define N1:Nat < N2:Nat => N1 <Int N2
  define N + infty => infty  
  define N1:Nat + N2:Nat => N1 +Int N2
endkm
