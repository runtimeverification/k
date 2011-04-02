kmod STACK-PATTERN is
  including MATCHC-SEMANTICS

  kvar F F1 F2 : Id
  kvar NeList1 NeList2 : NeList

  rule
    inStack(F, NeList1 NeList2) => inStack(F, NeList1) \/ inStack(F, NeList2)
  [structural print "\{print\} inStack split"]
  rule inStack(F1, callContext(F2, _, _, _)) => @(F1 ==Bool F2) [structural]
  rule inStack(F1, .List) => FalseFormula [structural]
endkm

