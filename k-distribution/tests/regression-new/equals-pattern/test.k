// Copyright (c) 2019 K Team. All Rights Reserved.

module TEST-SYNTAX
  imports INT
  imports K-EQUAL

syntax KItem ::= foo(Int) | bar(Int) | baz(KItem) | stuff(K)

syntax Constant ::= StringLiteral(K) | WStringLiteral(K)

rule I:Int => foo(_) :=K foo(I)
  requires I ==Int 0

rule 1 => foo(_) :/=K foo(0)

rule foo(I:Int) => #fun(0 => I ==Int 0)(0)

rule bar(A:Int) => #fun(bar(I => #fun(N => N +Int A)(I)))(bar(A))
  requires A <Int 2

rule baz(A:KItem) => #fun(baz(B) => baz(bar(_)) :=K baz(B))(baz(A))
  requires baz(_) :/=K A
rule baz(baz(A:KItem)) => #fun(baz(B) => baz(A) :=K baz(B))(baz(A))

rule stuff(K) => 10
          requires StringLiteral(...) :/=K K
               andBool WStringLiteral(...) :/=K K
rule stuff(K) => 10
          requires StringLiteral(...) :=K K
               andBool WStringLiteral(...) :=K K
endmodule

module TEST
  imports TEST-SYNTAX
endmodule
