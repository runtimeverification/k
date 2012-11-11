require "builtins.k"

module SYMBOLIC-K
  imports BUILTIN-HOOKS

  rule
    isSymbolicK(KL:KLabel(LK:List{K}))
  =>
    #if substrString(KLabel2String(KL), 0, 5) ==String "'#sym" #then
      true
    #else
      isSymbolicK(LK)
    #fi
  [predicate]
  rule
    isSymbolicK(K1:K ~> K2:K)
  =>
    isSymbolicK(K1) orElseBool isSymbolicK(K2)
  when K1 =/=K .K andThenBool K2 =/=K .K
  [predicate]
  rule isSymbolicK(.K) => false [predicate]

  rule
    isSymbolicK(K1:K,,K2:K,,LK:List{K})
  =>
    isSymbolicK(K1) orElseBool isSymbolicK(K2) orElseBool isSymbolicK(LK)
  [predicate]
  rule isSymbolicK(.List{K}) => false [predicate]
endmodule

