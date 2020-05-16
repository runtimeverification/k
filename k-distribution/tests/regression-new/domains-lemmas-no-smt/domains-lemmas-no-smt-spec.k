requires "domains-lemmas-no-smt.k"

module DOMAINS-LEMMAS-NO-SMT-SPEC
    imports DOMAINS-LEMMAS-NO-SMT

    // Arithmetic Normalization
    rule <k> 0 +Int X            => X                 ... </k>
    rule <k> (5 +Int X) +Int 0   => X +Int 5          ... </k>
    rule <k> X -Int (5 -Int 5)   => X                 ... </k>
    rule <k> 5 +Int X            => X +Int 5          ... </k>
    rule <k> X -Int 5            => X +Int (0 -Int 5) ... </k>
    rule <k> (X +Int 3) +Int 5   => X +Int 8          ... </k>
    rule <k> 3 +Int (X +Int 5)   => X +Int 8          ... </k>
    rule <k> 5 -Int (X +Int 3)   => 2 -Int X          ... </k>
    rule <k> 5 +Int (3 +Int X)   => 8 +Int X          ... </k>
    rule <k> 5 +Int (3 -Int X)   => 8 -Int X          ... </k>
    rule <k> (5 -Int X) +Int 3   => 8 -Int X          ... </k>
    rule <k> 5 -Int (3 +Int X)   => 2 -Int X          ... </k>
    rule <k> 5 -Int (3 -Int X)   => 2 +Int X          ... </k>
    rule <k> (X -Int 5) -Int 3   => X -Int 8          ... </k>
    rule <k> 5 &Int (3 &Int X)   => 1 &Int X          ... </k>
    rule <k> ((X +Int 1) +Int 1) => X +Int 2          ... </k>
endmodule
