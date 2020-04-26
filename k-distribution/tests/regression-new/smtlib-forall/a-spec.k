module A-SPEC

imports A

rule <k> foo(L) => 0 ... </k>
requires forall(x, L, x >Int 10)
 ensures forall(x, L, x >Int 0)

endmodule
