module K-VISITOR
  imports K-WRAPPERS
  syntax K ::= "visit" List{K} "applying" KLabel "if" KLabel
    [latex("\mbox{apply }{#2}\mbox{ in }{#1}\mbox{ if }{#3}"_)]
             | "visiting" List{K} "applying" KLabel "if" KLabel
    [latex("\mbox{apply }{#2}\mbox{ in }{#1}\mbox{ if }{#3}")]
  --- "boxed" versions of the K constructors (all of them are strict)
  syntax K ::= K "visitedL(~>)" K [latex("{#1}\framebox{$\kra$}{#2}"), strict]
             | K "visitedL(,,)" K [latex("{#1}\framebox{$,\!\!,$}{#2}"), strict]
  syntax KResult ::= "visitedK" List{K}  [latex("\framebox{${#1}$}")]

  rule visit Kl applying A if Pred:KLabel
    => #if Pred(Kl) ==K true 
       #then A(Kl) 
       #else visiting Kl applying A if Pred 
       #fi
   [structural]

  rule visiting Label(Kl) applying A if Pred
    => visitedL(Label)(visit Kl applying A if Pred)
    [structural]
    
  rule visiting . applying A:KLabel if Pred => visitedK(.) 
    [structural]
  rule visiting K1 ~> K2 applying A if Pred 
    => visit K1 applying A if Pred
    visitedL(~>) 
       visit K2 applying A if Pred
   when K1 =/=K . andBool  K2 =/=K . 
    [structural]
  rule visiting .List{K} applying A if Pred 
    => visitedK(.List{K}) 
    [structural]
  rule visiting K1,,NeKl:NeList`{K`} applying A if Pred
    => visit K1 applying A if Pred
    visitedL(,,) 
       visit NeKl applying A if Pred
    [structural]
    
  syntax KLabel ::= "visitedL" ( KLabel ) [latex("\framebox{#1}")]
  context visitedL(Label:KLabel)(_,,HOLE,,_)

  syntax K ::= "endVisit" K [strict, latex("{\it unbox}({#1})")]
  rule endVisit(visitedK(K:K)) => K [structural] 

  rule visitedL(Label)(visitedK(Kl:List`{K`})) => visitedK(Label(Kl)) [structural]
  rule visitedK(Kl) visitedL(,,) visitedK(Kl':List`{K`}) => visitedK((Kl,,Kl')) [structural]
  rule visitedK(K1:K) visitedL(~>) visitedK(K2:K) => visitedK((K1 ~> K2)) [structural]

endmodule
