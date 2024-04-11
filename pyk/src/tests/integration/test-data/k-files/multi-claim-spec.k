module MULTI-CLAIM-SYNTAX
    syntax Pgm ::= "a" | "b" | "c"
endmodule

module MULTI-CLAIM
    imports MULTI-CLAIM-SYNTAX

    configuration <k> $PGM:Pgm </k>
endmodule

module MULTI-CLAIM-SPEC-DEPENDENCY-1
    imports MULTI-CLAIM

    claim [dep-1.1]: <k> a => b </k>
endmodule

module MULTI-CLAIM-SPEC-DEPENDENCY-2
    imports MULTI-CLAIM

    claim [dep-2.1]: <k> b => c </k>

    claim [dep-2.2]: <k> b => c </k> [depends(MULTI-CLAIM-SPEC-DEPENDENCY-1.dep-1.1)]

    claim [rep-dep]: <k> c => b </k>
endmodule

module MULTI-CLAIM-SPEC
    imports MULTI-CLAIM-SPEC-DEPENDENCY-1
    imports MULTI-CLAIM-SPEC-DEPENDENCY-2

    claim <k> a => b </k>

    claim <k> a => c </k>

    claim [dep]: <k> c => a </k>

    claim [main.1]: <k> a => c </k> [depends(dep,MULTI-CLAIM-SPEC-DEPENDENCY-1.dep-1.1)]

    claim [main.3]: <k> a => c </k> [depends(MULTI-CLAIM-SPEC.dep)]

    claim [rep-dep]: <k> c => b </k>
endmodule

module MULTI-CLAIM-BROKEN-SPEC
    imports MULTI-CLAIM-SPEC

    claim [bad-dep]: <k> a => b </k> [depends(non-existent-1)]
endmodule
