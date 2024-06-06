module TEST
  imports INT
  imports BOOL
  imports LIST

syntax List ::= foo() [macro]
rule foo() => .List

rule true => size(ListItem(?X:Int) ?L:List)

rule I:Int => false requires I >=Int -1

rule size(L:List) >=Int 0 => true [simplification, smt-lemma]

endmodule
