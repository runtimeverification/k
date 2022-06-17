module CHECKEXCLUDESIMPLIFICATION-SYNTAX
endmodule

module CHECKEXCLUDESIMPLIFICATION
  imports CHECKEXCLUDESIMPLIFICATION-SYNTAX
  imports INT

syntax Int ::= f(Int)  [function, functional, no-evaluators]
syntax Int ::= g(Int)  [function, functional]

rule g(f(X)) => X [simplification]

endmodule
