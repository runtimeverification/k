kmod STACK-PATTERN is
  including MATCHC-SEMANTICS + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE

  kvar F F1 F2 : Id
  kvar NeList1 NeList2 : NeList

  op ids : List -> Seq++

  rule ids(NeList1 NeList2) => ids(NeList1) @ ids(NeList2) [structural]
  rule ids(callContext(F, _, _, _)) => [obj(F)] [structural]
  rule ids(.List) => epsilon [structural]
/*
  rule
    inStack(F, NeList1 NeList2) => inStack(F, NeList1) \/ inStack(F, NeList2)
  [structural print "\{print\} inStack split"]
  rule inStack(F1, callContext(F2, _, _, _)) => @(F1 ==Bool F2) [structural]
  rule inStack(F, .List) => FalseFormula [structural]

  rule topStack(F, NeList1 NeList2) => topStack(F, NeList1) [structural]
  rule topStack(F1, callContext(F2, _, _, _)) => @(F1 ==Bool F2) [structural]
  rule topStack(F, .List) => FalseFormula [structural]
*/
endkm

