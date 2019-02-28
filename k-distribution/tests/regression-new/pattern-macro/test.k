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

endmodule
