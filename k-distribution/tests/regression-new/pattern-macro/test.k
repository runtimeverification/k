module TEST
  imports INT
  imports BOOL

syntax SimpleType ::= "int" | "float" | "double"

syntax Type ::= t(m1: Int, m2: Int, st: SimpleType)

syntax Type ::= "floatingType" | "intType"

rule floatingType => t(?_, ?_, (float #Or double)) [macro]

rule floatingType => .K

rule intType => t(?Foo, ?Foo, int) [macro]

rule intType => .K

syntax RHold ::= te(K, Type)
syntax RValue ::= tv(K, Type)
syntax KItem ::= RValue
syntax KItem ::= RHold
syntax KItem ::= Type

syntax Expression ::= arithOp(K, K) | stuff(K)
rule arithOp(L:K, R:K) => stuff(L) [macro]
rule arithOp(L:RValue, R::RValue) => .K
rule arithOp(te(t(0, 0, int), t(0, 0, int)), R::RValue) => .K

syntax Expression ::= stuff2(K)
rule stuff2(_:K) => 0 [macro]
rule stuff2(.K) => 1

endmodule
