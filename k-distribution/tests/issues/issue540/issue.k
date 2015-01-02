// Copyright (c) 2012-2015 K Team. All Rights Reserved.
module ISSUE

  syntax Exp ::= Exp "[" Exp "]"
  syntax KItem ::= addArg(Exp, Exp)

  rule E in E2 => addArg(.K, E[E2:K])

endmodule
