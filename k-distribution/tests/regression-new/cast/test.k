module TEST
  imports INT

syntax KItem ::= Int

syntax K ::= value(K) [function]
syntax RValue ::= te(K)

syntax Int ::= asInt(RValue) [function]
syntax Int ::= foo(Int) [function]

rule value(te(K:K)) => K

rule asInt(V::RValue) => foo({value(V)}:>Int)
rule foo(I:Int) => I

endmodule
