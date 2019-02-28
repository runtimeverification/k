module TEST
  imports SET
  imports BOOL

syntax SimpleType ::= "int" | "float" | "double"

syntax Type ::= t(m: Set, st: SimpleType)

syntax Type ::= "floatingType"

rule floatingType => t(?_, (float #Or double)) [macro]

rule floatingType => .K

endmodule
