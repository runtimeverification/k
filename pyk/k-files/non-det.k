module NON-DET-SYNTAX
endmodule

module NON-DET
    imports INT

    syntax A ::= "a" | "b" | "c" | d(Int) | e(Int) | "f"

    // Raw non-determinism
    rule a => b
    rule a => c

    // Split on new symbolic variable
    rule c => d(?I) ensures ?I >Int 0
    rule c => e(?I) ensures ?I <=Int 0

    // Make it easy to write a claim
    rule b => f
    rule d(_) => f
    rule e(_) => f
endmodule
