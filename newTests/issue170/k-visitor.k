require ../../k-prelude
kmod K-VISITOR is including K + K-WRAPPERS
  syntax K ::= visit List{K} applying KLabel if label in Set 
    [latex "\mbox{apply }{#2}\mbox{ to }{#3}\mbox{ in }{#1}"]
  --- "boxed" versions of the K constructors (all of them are strict)
  syntax K ::= K visitedL(~>) K [latex "{#1}\framebox{$\kra$}{#2}" strict]
             | K visitedL(,,) K [latex "{#1}\framebox{$,\!\!,$}{#2}" strict]
  syntax KResult ::= visitedK List{K}  [latex "\framebox{${#1}$}"]

  rule visit Label(Kl) applying A if label in Labels SetItem(wklabel(Label))
    => A(Label(Kl)) [structural]
  rule visit Label(Kl) applying A if label in Labels
    => visitedL(Label)(visit Kl applying A if label in Labels)
    if notBool(wklabel(Label) in Labels)  
    [structural]
    
  rule visit . applying A:KLabel if label in Labels:Set => visitedK(.) 
    [structural]
  rule visit K1 ~> K2 applying A if label in Labels 
    => visit K1 applying A if label in Labels
    visitedL(~>) 
       visit K2 applying A if label in Labels
    if K1 =/=Bool . andBool  K2 =/=Bool . 
    [structural]
  rule visit .List{K} applying A if label in Labels 
    => visitedK(.List{K}) 
    [structural]
  rule visit K1,,NeKl:NeList`{K`} applying A if label in Labels
    => visit K1 applying A if label in Labels
    visitedL(,,) 
       visit NeKl applying A if label in Labels
    [structural]
    
  syntax KLabel ::= visitedL ( KLabel ) [latex "\framebox{#1}"]
  context visitedL(Label:KLabel)(_,,`[HOLE`]:K,,_)

  syntax K ::= endVisit K [strict latex "{\it unbox}({#1})"]
  rule endVisit(visitedK(K:K)) => K [structural] 

  rule visitedL(Label)(visitedK(Kl:List`{K`})) => visitedK(Label(Kl)) [structural]
  rule visitedK(Kl) visitedL(,,) visitedK(Kl':List`{K`}) => visitedK((Kl,,Kl')) [structural]
  rule visitedK(K1:K) visitedL(~>) visitedK(K2:K) => visitedK((K1 ~> K2)) [structural]
  
endkm