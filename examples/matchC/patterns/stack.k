kmod STACK-PATTERN is
  including MATCHC-SEMANTICS + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE

  kvar F F1 F2 : Id
  kvar NeList1 NeList2 : NeList

  op ids : List -> NeSeq++

  rule ids(NeList1 NeList2) => ids(NeList1) @ ids(NeList2) [structural]
  rule ids(callContext(F, _, _, _)) => [obj(F)] [structural]
  rule ids(.List) => epsilon [structural]
endkm

