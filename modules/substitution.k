require k-visitor

module SUBSTITUTION 
  imports K-VISITOR
---beta-substitution definition using the K AST visitor pattern
  syntax K ::= #Id  | #Nat
             | K [ K / #Id ] [prec 0]
             | beta K [ K / #Id ]
               [prec 0 latex "{#1}\sqbracket{\framebox{${#2}$}/{#3}}"]
             | eval K , then apply [ K / #Id ]  
               [prec 0 strict(1) latex "eval({#1})\sqbracket{\framebox{${#2}$}/{#3}}"]
               
  syntax KLabel ::= beta [ K / #Id ] 
               [prec 0 latex "\sqbracket{\framebox{${#1}$}/{#2}}"]
                  | isBinder
                  | isBinder or #Id
               
  rule isBinder or X(X) => true
  rule isBinder or X(K) => true if isBinder(K)
  
  syntax #Id ::= id #Nat  --- to generate fresh names
  rule id N:#Nat => #id ("id" +String Int2String(N))
  configuration <k color="green"> .K </k> <nextId> 0 </nextId>

  rule <k> K'[K/Y] => endVisit(beta K'[K/Y]) <_/k> [structural]

  rule beta[K/Y](Y) => visitedK(K) [structural]  ---this does the actual substitution

  rule <k> beta[K/Y](L:KLabel(X:#Id,,K')) => 
           visitedL(L)(visitedK(id(N)) 
                visitedL(,,) eval (beta K' [id(N)/X]), then apply [K/Y])
      <_/k> <nextId>N:#Nat => sNat N</nextId>
---    if Y =/=Bool X [structural] ---renaming bound variables
  rule eval visitedK(K'), then apply [ K / Y ] => beta K'[K/Y] [structural]

  macro beta K':K [K:K/Y:#Id] 
      = visit K' applying beta[K/Y] 
                       if isBinder or Y

end module
