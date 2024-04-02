module REFUTE-NODE-SYNTAX
    imports INT

    syntax A ::= a(Int) | b(Int) | c(Int) | d(Int) | e(Int) | f(Int) | g(Int, Int, Int) | h(Int, Int)

endmodule

module REFUTE-NODE
    imports REFUTE-NODE-SYNTAX

    rule <k> d(N) => e(N +Int 1) ... </k> requires N >Int 0
    rule <k> d(N) => e(N -Int 1) ... </k> requires N <=Int 0

    rule <k> a(N) => b(N) ... </k> requires N >Int 0
    rule <k> a(N) => c(N) ... </k> requires N <=Int 0
    rule <k> b(N) => f(N) ... </k>
    rule <k> c(N) => f(N) ... </k>

    rule <k> g(L, _, N) => e(N +Int 1) ... </k> requires L >Int 0
    rule <k> g(L, M, N) => h(M, N) ... </k> requires L <=Int 0
    rule <k> h(M, N) => e(N +Int 1) ... </k> requires M >Int 0
    rule <k> h(M, N) => d(N) ... </k> requires M <=Int 0

endmodule
