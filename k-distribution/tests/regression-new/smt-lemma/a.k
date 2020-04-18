// Copyright (c) 2020 K Team. All Rights Reserved.

module A

imports INT

syntax Int ::= foo(Int) [function, smtlib(foo)]
             | bar(Int) [function, smtlib(bar)]

rule foo(X) => bar(X) requires X >Int 0 [concrete, smt-lemma]

syntax KItem ::= zoo(Int)
               | koo(Int)

rule zoo(X) => koo(X)

endmodule
