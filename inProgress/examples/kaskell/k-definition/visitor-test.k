in haskell-syntax.k
in ../../../modules/k-visitor.k

kmod VISITOR-TEST is including HASKELL-SYNTAX + K + K-VISITOR + PL-NAT

  configuration <T> <k> .K </k> <counter> 0 </counter> <stage> 0 </stage> </T>

  syntax K ::= test1 | test2
  macro test1 = NegApp (Lit (Int 42))
  macro test2 = InfixApp (NegApp (Lit (Int 2))) (QVarOp (UnQual (Symbol "+"))) (NegApp (Lit (Int 3)))

  syntax K ::= translate K
  syntax KLabel ::= count

  macro translate K = visit K applying count if label in SetItem(wklabel('NegApp_))

  rule <k> K:K => endVisit translate K </k>  <stage> 0 => 1 </stage>
  rule <k_> count(NegApp K) => visitedL('NegApp_)(translate K) <_/k> <counter> N:Nat => sNat N </counter>


  syntax Bag ::= [[ KLabel ]]
  macro [[KL:KLabel]] = <T_> <k> KL(.List{K}) </k> <_/T>

endkm
