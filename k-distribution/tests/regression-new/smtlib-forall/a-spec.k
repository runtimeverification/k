module A-SPEC

imports A

rule <k> foo(L) => 0 ... </k>
requires forall(x, L, x >Int 10)
 ensures forall(x, L, x >Int 0)

rule <k> bar(L1, L2) => 0 ... </k>
requires forall(x, L1, forall(y, L2, x >Int y))
 ensures forall(x, L2, forall(y, L1, x <Int y))

endmodule
