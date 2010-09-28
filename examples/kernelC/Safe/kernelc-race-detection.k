kmod KERNELC-RACE-DETECTION is  including  BASIC-KERNELC-SEMANTICS
  syntax CellLabel ::= race
  rule < T => race >... < k => race > * N:Nat = E:Exp ...</ k => race > < k => race > * N:Nat = E':Exp ...</ k => race > ...</ T => race > [structural]
  rule < T => race >... < k => race > * N:Nat = E:Exp ...</ k => race > < k => race > * N:Nat ...</ k => race > ...</ T => race > [structural]
endkm
