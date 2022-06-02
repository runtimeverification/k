// Copyright (c) 2022 K Team. All Rights Reserved.

module SET-TESTS-SYNTAX
    imports SET
    imports INT
    imports K-EQUAL
    imports BOOL

    syntax MyId ::= "x" | "y" | "z" | foo ( MyId )

    syntax Test ::= union       ( Set ) | inSet       ( Bool ) | diff       ( Set )
                  | unionResult ( Set ) | inSetResult ( Bool ) | diffResult ( Set )
endmodule

module SET-TESTS
    imports SET-TESTS-SYNTAX
    imports SET-SYMBOLIC

    configuration <k> $PGM:Test </k>

    rule <k> union ( S ) => unionResult ( S ) </k>
    rule <k> inSet ( B ) => inSetResult ( B ) </k>
    rule <k> diff  ( S ) => diffResult  ( S ) </k>
endmodule
