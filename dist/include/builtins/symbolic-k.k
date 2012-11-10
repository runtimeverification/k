require "builtins.k"

module SYMBOLIC-K
  imports BUILTINS-HOOKS

  rule
    isSymbolicK(KL:KLabel(L:List{K}))
  =>
    #if #then
      isSymbolicK(L)
    #else
      true
    #fi

endmodule

