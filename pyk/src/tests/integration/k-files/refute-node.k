module REFUTE-NODE-SYNTAX
    imports INT

    syntax A ::= a(Int) | b(Int) | c(Int) | d(Int) | e(Int) | f(Int)
endmodule

module REFUTE-NODE
    imports REFUTE-NODE-SYNTAX

    rule <k> d(N) => e(N +Int 1) ... </k> requires N >Int 0
    rule <k> d(N) => e(N -Int 1) ... </k> requires N <=Int 0

    rule <k> a(N) => b(N) ... </k> requires N >Int 0
    rule <k> a(N) => c(N) ... </k> requires N <=Int 0
    rule <k> b(N) => f(N) ... </k>
    rule <k> c(N) => f(N) ... </k>

endmodule
