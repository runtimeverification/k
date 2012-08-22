module K-VISITOR
  imports BUILTIN-HOOKS
  syntax K ::= "visit" List{K} "applying" KLabel "if" KLabel
    [latex(\mbox{apply }{#2}\mbox{ in }{#1}\mbox{ if }{#3})]
             | "visiting" List{K} "applying" KLabel "if" KLabel
    [latex(\mbox{apply }{#2}\mbox{ in }{#1}\mbox{ if }{#3})]
  // "boxed" versions of the K constructors (all of them are strict)
  syntax K ::= K "visitedL(~>)" K [latex({#1}\framebox{$\kra$}{#2}), strict]
             > K "visitedL(,,)" K [latex({#1}\framebox{$,\!\!,$}{#2}), strict]
  syntax KResult ::= "visitedK" "(" List{K} ")" [latex(\framebox{${#1}$})]

  rule visit Kl:List{K} applying A:KLabel if Pred:KLabel
    => #if Pred:KLabel(Kl:List{K}) ==K true 
       #then A:KLabel(Kl:List{K}) 
       #else visiting Kl:List{K} applying A:KLabel if Pred:KLabel 
       #fi
   [structural]

  rule visiting Label:KLabel(Kl:List{K}) applying A:KLabel if Pred:KLabel
    => visitedL(Label:KLabel)(visit Kl:List{K} applying A:KLabel if Pred:KLabel)
    [structural]
    
  rule visiting . applying A:KLabel if Pred:KLabel => visitedK(.) 
    [structural]
  rule visiting K1 ~> K2 applying A:KLabel if Pred:KLabel 
    => visit K1 applying A:KLabel if Pred:KLabel
    visitedL(~>) 
       visit K2 applying A:KLabel if Pred:KLabel
   when K1 =/=K . andBool  K2 =/=K . 
    [structural]
  rule visiting .List{K} applying A:KLabel if Pred:KLabel 
    => visitedK(.List{K}) 
    [structural]
  rule visiting K1:K,,NeKl:List{K} applying A:KLabel if Pred:KLabel
    => visit K1:K applying A:KLabel if Pred:KLabel
    visitedL(,,) 
       visit NeKl:List{K} applying A:KLabel if Pred:KLabel
    when NeKl =/=List{K} .List{K}
    [structural]
    
  syntax KLabel ::= "visitedL" "(" KLabel ")" [latex(\framebox{#1})]
  context visitedL(Label:KLabel)(_,,HOLE,,_)

  syntax K ::= "endVisit" K [strict, latex({\it unbox}({#1}))]
  rule endVisit(visitedK(K:K)) => K [structural] 

  rule visitedL(Label:KLabel)(visitedK(Kl:List{K})) => visitedK(Label:KLabel(Kl:List{K})) [structural]
  rule visitedK(Kl:List{K}) visitedL(,,) visitedK(Kl':List{K}) => visitedK((Kl:List{K},,Kl':List{K})) [structural]
  rule visitedK(K1:K) visitedL(~>) visitedK(K2:K) => visitedK((K1 ~> K2)) [structural]

endmodule
