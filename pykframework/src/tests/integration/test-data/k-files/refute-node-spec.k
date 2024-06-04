requires "refute-node.k"

module REFUTE-NODE-SPEC
    imports REFUTE-NODE

    claim [split-int-fail]: <k> d(N) => e(N +Int 1) ... </k>

    claim [split-int-succeed]: <k> a(N) => f(N) ... </k>

    claim [triple-split-int-fail]: <k> g(L +Int N, M, N) => e(N +Int 1) ... </k>

    claim [multi-constraint-split]: <k> g(L, M, N) => e(N +Int 1) ... </k>
endmodule
