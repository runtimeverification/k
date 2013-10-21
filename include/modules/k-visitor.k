require "builtins/k-equal.k"


module K-VISITOR
  imports K-EQUAL-HOOKS
  imports BUILTIN-HOOKS

  syntax K ::= "visit" KList "applying" KLabel "if" KLabel
    [latex(\mbox{apply }{#2}\mbox{ in }{#1}\mbox{ if }{#3})]
             | "visiting" KList "applying" KLabel "if" KLabel
    [latex(\mbox{apply }{#2}\mbox{ in }{#1}\mbox{ if }{#3})]
  // "boxed" versions of the K constructors (all of them are strict)
  syntax K ::= K "visitedL(~>)" K [latex({#1}\framebox{$\kra$}{#2}), strict]
             > K "visitedL(,,)" K [latex({#1}\framebox{$,\!\!,$}{#2}), strict]
  syntax KResult ::= "visitedK" "(" KList ")" [latex(\framebox{${#1}$})]

  rule visit Kl:KList applying A:KLabel if Pred:KLabel
    => #if Pred:KLabel(Kl:KList) ==K true 
       #then A:KLabel(Kl:KList) 
       #else visiting Kl:KList applying A:KLabel if Pred:KLabel 
       #fi
   [structural]

  rule visiting Label:KLabel(Kl:KList) applying A:KLabel if Pred:KLabel
    => visitedL(Label:KLabel)(visit Kl:KList applying A:KLabel if Pred:KLabel)
    [structural]
    
  rule visiting . applying A:KLabel if Pred:KLabel => visitedK(.) 
    [structural]
  rule visiting K1 ~> K2 applying A:KLabel if Pred:KLabel 
    => visit K1 applying A:KLabel if Pred:KLabel
    visitedL(~>) 
       visit K2 applying A:KLabel if Pred:KLabel
   when K1 =/=K . andBool  K2 =/=K . 
    [structural]
  rule visiting .KList applying A:KLabel if Pred:KLabel 
    => visitedK(.KList) 
    [structural]
  rule visiting K1:K,,NeKl:KList applying A:KLabel if Pred:KLabel
    => visit K1:K applying A:KLabel if Pred:KLabel
    visitedL(,,) 
       visit NeKl:KList applying A:KLabel if Pred:KLabel
    when NeKl =/=KList .KList
    [structural]
    
  syntax KLabel ::= "visitedL" "(" KLabel ")" [latex(\framebox{#1})]
  context visitedL(Label:KLabel)(_,,HOLE,,_)

  syntax K ::= "endVisit" K [strict, latex({\it unbox}({#1}))]
  rule endVisit(visitedK(K:K)) => K [structural] 

  rule visitedL(Label:KLabel)(visitedK(Kl:KList)) => visitedK(Label:KLabel(Kl:KList)) [structural]
  rule visitedK(Kl:KList) visitedL(,,) visitedK(Kl':KList) => visitedK((Kl:KList,,Kl':KList)) [structural]
  rule visitedK(K1:K) visitedL(~>) visitedK(K2:K) => visitedK((K1 ~> K2)) [structural]

endmodule
