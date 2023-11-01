// Copyright (c) K Team. All Rights Reserved.
module TEST

syntax KItem ::= foo(KItem)

rule foo((foo(G:KItem) => foo(foo(G))))
endmodule
