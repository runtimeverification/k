// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
module TEST
  imports DOMAINS

configuration <k> $PGM:K </k>

syntax Foo ::= "foo" | "bar"

rule foo => #if ?_B:Bool #then 0 #else 1 #fi ~> 0

rule _I:Int => bar

endmodule
