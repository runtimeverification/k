// Copyright (c) 2018-2019 K Team. All Rights Reserved.
module TEST
  imports DOMAINS

configuration <k> $PGM:K </k>

syntax Foo ::= "foo" | "bar"

rule foo => #if ?B:Bool #then 0 #else 1 #fi ~> 0

rule I:Int => bar

endmodule
