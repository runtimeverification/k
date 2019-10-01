// Copyright (c) 2018-2019 K Team. All Rights Reserved.
module TEST
  imports DOMAINS

configuration <k> $PGM:K </k>

syntax Foo ::= foo ( Bool ) | "bar" | "baz"

rule foo(B) => #if1 B #then bar #else baz #fi

syntax K ::= "#if1" Bool "#then" K "#else" K "#fi"   [function, poly(0, 2, 3)]
rule #if1 C:Bool #then B1::K #else _ #fi => B1 requires C
rule #if1 C:Bool #then _ #else B2::K #fi => B2 requires notBool C

endmodule
