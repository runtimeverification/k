module TEST

syntax KItem ::= foo(KItem)

rule foo((foo(G:KItem) => foo(foo(G))))
endmodule
