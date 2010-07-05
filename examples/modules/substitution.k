kmod SUBSTITUTION is including PL-ID + PL-INT + K-VISITOR
---beta-substitution definition using the K AST visitor pattern
---assuming the binding operator is [_]_
  syntax K ::= Id | [ Id ] K | Nat
             | K [ K / Id ] [prec 0]
             | beta K [ K / Id ]
               [prec 0 latex "{#1}\sqbracket{{#2}/_\beta{#3}}"]
             | beta-beta K [ K / Id ]  
               [prec 0 strict(1) latex "eval({#1})\sqbracket{{#2}/_\beta{#3}}"]
               
  syntax KLabel ::= beta [ K / Id ] 
               [prec 0 latex "\sqbracket{{#1}/_\beta{#2}}"]
               
  syntax Id ::= id Nat [latex "{\it id}_{{#1}}"] --- to generate fresh names
  configuration <k> .K </k> <nextId> 0 </nextId>

  rule <k> K'[K/Y] => endVisit(beta K'[K/Y]) <_/k> [structural]

  rule beta[K/Y](Y) => visitedK(K) [structural]  ---this does the actual substitution

  rule <k> beta[K/Y]([X:Id]K') => 
           visitedL('`[_`]_)(visitedK(id(N)) 
                visitedL(,,) beta-beta (beta K' [id(N)/X])[K/Y])
      <_/k> <nextId>N:Nat => sNat N</nextId>
---    if Y =/=Bool X [structural] ---renaming bound variables
  rule beta-beta visitedK(K')[K/Y] => beta K'[K/Y] [structural]

  macro beta K':K [K:K/Y:Id] 
      = visit K' applying beta[K/Y] 
                       if label in Set(wklabel('`[_`]_),,wklabel(getKLabel(Y)))

endkm
