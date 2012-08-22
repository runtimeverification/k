require "k-visitor.k"

module BINDER
  imports BUILTIN-HOOKS
  syntax KLabel ::= "isBinder"
                  | "isBinder" "or" Id

  rule isBinder or X(X:Id) => true [function, anywhere]
  rule isBinder or X(K:K) => true when isBinder(K) [function, anywhere]
endmodule

module SUBSTITUTION 
  imports K-VISITOR
  imports BINDER

  //beta-substitution definition using the K AST visitor pattern
  syntax K ::= K "[" K "/" Id "]"
             | "beta" K "[" K "/" Id "]" [latex({#1}\sqbracket{\framebox{${#2}$}/{#3}})]
             | "eval" K "," "then" "apply" "[" K "/" Id "]" [strict(1), latex(eval({#1})\sqbracket{\framebox{${#2}$}/{#3}})]
               
  syntax KLabel ::= "beta" "[" K "/" Id "]" 
            [latex(\sqbracket{\framebox{${#1}$}/{#2}})]
               
  syntax Id ::= "id" Int  [function]   // to generate fresh names
  rule id N:Nat => String2Id("_id" +String Int2String(N)) [function, anywhere]

  rule <k> K'[K/Y] => endVisit(beta K'[K/Y]) ...</k> [structural]

  rule beta[K/Y](Y) => visitedK(K) [structural]  //this does the actual substitution

  syntax CellLabel ::= "nextId"

  rule <k> beta[K/Y](L:KLabel(X:Id,,K')) => 
           visitedL(L)(visitedK(id(N)) 
                visitedL(,,) eval (beta K' [id(N)/X]), then apply [K/Y])
      ...</k> <nextId>N:Nat => N +Int 1 </nextId>
//   when Y =/=Bool X [structural] //renaming bound variables
  rule eval visitedK(K'), then apply [ K / Y ] => beta K'[K/Y] [structural]

  // This was a macro 

  rule beta K':K [K:K/Y:Id]
    => visit K' applying beta[K/Y] if isBinder or Y
    [structural]
endmodule
