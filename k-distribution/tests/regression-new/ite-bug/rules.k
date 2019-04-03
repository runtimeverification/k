requires "./ite-bug.k"

module RULES
  imports ITE-BUG

  rule bool2Word(A)  ==K 0 => notBool(A)
  rule bool2Word(A)  ==K 1 => A
endmodule