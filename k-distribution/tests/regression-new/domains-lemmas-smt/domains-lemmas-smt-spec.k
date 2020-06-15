requires "domains-lemmas-smt.k"

module DOMAINS-LEMMAS-SMT-SPEC
    imports DOMAINS-LEMMAS-SMT

    // Arithmetic Normalization
    rule <k> (4 +Int X) modInt 10 => 4 +Int X ... </k> requires -4 <=Int X andBool X <Int 6
    rule <k> (4 +Int X)   %Int 10 => 4 +Int X ... </k> requires -4 <=Int X andBool X <Int 6
endmodule
