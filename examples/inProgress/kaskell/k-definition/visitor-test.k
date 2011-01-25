in haskell-syntax.k
in ../../../modules/k-visitor.k

kmod VISITOR-TEST is including HASKELL-SYNTAX + K + K-VISITOR + PL-NAT

  configuration <T> <k> .K </k> <counter> 0 </counter> </T>

  syntax K ::= test1 | test2
  macro test1 = NegApp (Lit (Int 42))
  macro test2 = InfixApp (NegApp (Lit (Int 2))) (QVarOp (UnQual (Symbol "+"))) (NegApp (Lit (Int 3)))

  syntax K ::= translate K
  syntax KLabel ::= count

  macro translate K = visit K applying count if label in SetItem(wklabel('NegApp_))

  rule <k> K:K => translate K </k>
  rule <k_> count(NegApp K) => NegApp K <_/k> <counter> N:Nat => sNat N </counter>


  syntax Bag ::= [[ KLabel ]]
  macro [[KL:KLabel]] = <T> <k> KL(.List{K}) </k> <counter> 0 </counter> </T>

endkm
