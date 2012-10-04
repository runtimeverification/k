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
             | "beta" List{K} "[" K "/" Id "]" [latex({#1}\sqbracket{\framebox{${#2}$}/{#3}})]
             | "eval" K "," "then" "apply" "[" K "/" Id "]" [strict(1), latex(eval({#1})\sqbracket{\framebox{${#2}$}/{#3}})]
               
  syntax KLabel ::= "beta" "[" K "/" Id "]" 
            [latex(\sqbracket{\framebox{${#1}$}/{#2}})]
               
//  syntax Id ::= "id" Int  [function]   // to generate fresh names
//  rule id N:Nat => String2Id("_id" +String Int2String(N)) [function, anywhere]

  rule Id2String('symId`(_`)(N:Int)) => "_id" +String Int2String(N) [anywhere]

  rule <k> K'[K/Y] => endVisit(beta K'[K/Y]) ...</k> [structural]

  rule beta[K/Y](Y) => visitedK(K) [structural]  //this does the actual substitution

//  syntax CellLabel ::= "nextId"

  rule beta[K/Y](L:KLabel(X:Id,,Ks)) => 
           visitedL(L)(visitedK(F) 
                visitedL(,,) eval (beta Ks [F/X]), then apply [K/Y])
      when fresh(F:Id) 
//     <nextId>N:Nat => N +Int 1 </nextId>
//   when Y =/=Bool X [structural] //renaming bound variables
  rule eval visitedK(K'), then apply [ K / Y ] => beta K'[K/Y] [structural]

  // This was a macro 

  rule beta Ks [K:K/Y:Id]
    => visit Ks applying beta[K/Y] if isBinder or Y
    [structural]
endmodule
