require k-visitor

module BINDER is
  syntax KLabel ::= isBinder
                  | isBinder or Id

  define isBinder or X(X:Id) => true
  define isBinder or X(K:K) => true when isBinder(K)
end module

module SUBSTITUTION 
  imports K-VISITOR
  imports BINDER
---beta-substitution definition using the K AST visitor pattern
  syntax K ::= K [ K / Id ] [prec 0]
             | beta K [ K / Id ]
               [prec 0 latex "{#1}\sqbracket{\framebox{${#2}$}/{#3}}"]
             | eval K , then apply [ K / Id ]  
               [prec 0 strict(1) latex "eval({#1})\sqbracket{\framebox{${#2}$}/{#3}}"]
               
  syntax KLabel ::= beta [ K / Id ] 
               [prec 0 latex "\sqbracket{\framebox{${#1}$}/{#2}}"]
               
  syntax Id ::= "id" Nat  [function]   --- to generate fresh names
---  declare id_ : Nat -> Id  --- to generate fresh names
  define id N:Nat => String2Id("_id" +String Int2String(N))

  syntax CellLabel ::= "nextId"

  rule <k> K'[K/Y] => endVisit(beta K'[K/Y]) <_/k> [structural]

  rule beta[K/Y](Y) => visitedK(K) [structural]  ---this does the actual substitution

  rule <k> beta[K/Y](L:KLabel(X:Id,,K')) => 
           visitedL(L)(visitedK(id(N)) 
                visitedL(,,) eval (beta K' [id(N)/X]), then apply [K/Y])
      <_/k> <nextId>N:Nat => N +Int 1 </nextId>
---   when Y =/=Bool X [structural] ---renaming bound variables
  rule eval visitedK(K'), then apply [ K / Y ] => beta K'[K/Y] [structural]

  macro beta K':K [K:K/Y:Id] 
      = visit K' applying beta[K/Y] 
                       if isBinder or Y

end module
