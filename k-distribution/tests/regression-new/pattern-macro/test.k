module TEST
  imports INT
  imports BOOL

syntax SimpleType ::= "int" | "float" | "double"

syntax Type ::= t(m1: Int, m2: Int, st: SimpleType)

syntax Type ::= "floatingType" [macro]
              | "intType"      [macro]

rule floatingType => t(_, _, (float #Or double)) [unboundVariables(_)]

rule <k> floatingType => .K </k>

rule intType => t(Foo, Foo, int) [unboundVariables(Foo)]

rule <k> intType => .K </k>

syntax RHold ::= te(K, Type)
syntax RValue ::= tv(K, Type)
syntax KItem ::= RValue
syntax KItem ::= RHold
syntax KItem ::= Type

syntax Expression ::= arithOp(K, K) [macro]
                    | stuff(K) | Int
rule arithOp(L:K, _R:K) => stuff(L)
rule <k> arithOp(_L:RValue, _R::RValue) => .K </k>
rule <k> arithOp(te(t(0, 0, int), t(0, 0, int)), _R::RValue) => .K </k>

syntax Expression ::= stuff2(K) [macro]
rule stuff2(_:K) => 0
rule <k> stuff2(.K) => 1 </k>

endmodule
