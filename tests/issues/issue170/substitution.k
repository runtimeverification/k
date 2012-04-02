require k-visitor

module SUBSTITUTION imports #ID + #INT + K-VISITOR
---beta-substitution definition using the K AST visitor pattern
---assuming the binding operator is [_]_
  syntax K ::= Id  | Nat
             | [ Id ] K [latex "{#1}.{#2}"]
             | K [ K / Id ] [prec 0]
             | beta K [ K / Id ]
               [prec 0 latex "{#1}\sqbracket{\framebox{${#2}$}/{#3}}"]
             | eval K , then apply [ K / Id ]  
               [prec 0 strict(1) latex "eval({#1})\sqbracket{\framebox{${#2}$}/{#3}}"]
               
  syntax KLabel ::= beta [ K / Id ] 
               [prec 0 latex "\sqbracket{\framebox{${#1}$}/{#2}}"]
               
  syntax Id ::= id Nat [latex "{\it id}_{\mbox{\scriptsize \ensuremath{#1}}}"] --- to generate fresh names
  configuration <k> .K </k> <nextId> 0 </nextId>

  rule <k> K'[K/Y] => endVisit(beta K'[K/Y]) <_/k> [structural]

  rule beta[K/Y](Y) => visitedK(K) [structural]  ---this does the actual substitution

  rule <k> beta[K/Y]([X:Id]K') => 
           visitedL('`[_`]_)(visitedK(id(N)) 
                visitedL(,,) eval (beta K' [id(N)/X]), then apply [K/Y])
      <_/k> <nextId>N:Nat => sNat N</nextId>
---    if Y =/=Bool X [structural] ---renaming bound variables
  rule eval visitedK(K'), then apply [ K / Y ] => beta K'[K/Y] [structural]

  macro beta K':K [K:K/Y:Id] 
      = visit K' applying beta[K/Y] 
                       if label in SetItem(wklabel('`[_`]_)) SetItem(wklabel(getKLabel(Y)))

end module
