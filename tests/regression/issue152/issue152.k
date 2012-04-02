in haskell-syntax.k
in /modules/k-visitor.k

module ISSUE152 imports HASKELL-SYNTAX + K-VISITOR 

  configuration <T> <k> .K </k> <counter> 0 </counter> <stage> 0 </stage> </T>

  syntax K ::= test1 
  macro test1 = NegApp (Lit (Int 42))

  syntax K ::= translate K
  syntax KLabel ::= count | predicate
  syntax Bag ::= finished

  rule predicate(NegApp K:K) => true

  macro translate K = visit K applying count if predicate

  rule <k> K:K => endVisit translate K </k>  <stage> 0 => 1 </stage>
  rule <k_> count(NegApp K) => visitedL('NegApp_)(translate K) <_/k> <counter> N:Nat =>  N +Int 1 </counter>
  rule <T>... <k> NegApp(Lit(Int(42))) </k> ...</T> => finished

  syntax Bag ::= [[ KLabel ]]
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>

end module
