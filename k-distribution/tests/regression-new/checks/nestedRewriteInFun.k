module NESTEDREWRITEINFUN
  imports INT

rule 0 => #fun(0 => 1)(0)
rule 0 => #fun(0 => (1 => 2))(0)
rule 0 => #fun((0 => 1) => 2)(0)

syntax Foo ::= foo(Int)

rule 1 => #fun(foo(0 => 1))(0)
rule 1 => #fun(foo(0 => (1 => 2)))(0)
rule 1 => #fun(foo((0 => 1) => 2))(0)

endmodule
