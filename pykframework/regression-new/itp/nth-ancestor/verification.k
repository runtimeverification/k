// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

requires "chain.k"

module VERIFICATION-SYNTAX
endmodule

module VERIFICATION
    imports VERIFICATION-SYNTAX
    imports CHAIN

    syntax Bool ::= const(Int) [function, smtlib(con), no-evaluators]

    syntax Int ::= k(Int) [function, total, injective, smtlib(k), no-evaluators]

    rule (k(N) +Int 1) -Int 1 => k(N) [simplification]
endmodule
