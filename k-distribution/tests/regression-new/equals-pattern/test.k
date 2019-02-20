module TEST
  imports INT
  imports K-EQUAL

syntax KItem ::= foo(Int) | bar(Int) | baz(KItem)

rule I:Int => foo(I) ==K foo(_)
  requires I ==Int 0

rule 1 => foo(0) =/=K foo(_)

rule foo(I:Int) => #fun(0 => I ==Int 0)(0)

rule bar(A:Int) => #fun(bar(I => #fun(N => N +Int A)(I)))(bar(A))
  requires A <Int 2

rule baz(A:KItem) => #fun(baz(B) => baz(B) ==K baz(bar(_)))(baz(A))
  requires A =/=K baz(_)
rule baz(baz(A:KItem)) => #fun(baz(B) => baz(B) ==K baz(A))(baz(A))

endmodule
