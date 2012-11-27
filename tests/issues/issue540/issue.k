module ISSUE

  syntax Exp ::= Exp "[" Exp "]"
  syntax K ::= addArg(Exp, Exp)

  rule E in E2 => addArg(.K, E[E2:K])

endmodule
