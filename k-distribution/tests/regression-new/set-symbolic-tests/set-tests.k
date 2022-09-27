// Copyright (c) 2022 K Team. All Rights Reserved.

module SET-TESTS-SYNTAX
    imports SET
    imports INT
    imports K-EQUAL
    imports BOOL

    syntax MyId ::= "x" | "y" | "z" | foo ( MyId )
    syntax Exp ::= Bool | Set

    syntax Test ::= inSet       ( Exp ) | union       ( Exp ) | diff       ( Exp ) | intersect       ( Exp )
                  | inSetResult ( Exp ) | unionResult ( Exp ) | diffResult ( Exp ) | intersectResult ( Exp )
endmodule

module SET-TESTS
    imports SET-TESTS-SYNTAX
    imports SET-SYMBOLIC

    configuration <k> $PGM:Test </k>

    rule <k> inSet     ( E ) => inSetResult     ( E ) </k>
    rule <k> union     ( E ) => unionResult     ( E ) </k>
    rule <k> diff      ( E ) => diffResult      ( E ) </k>
    rule <k> intersect ( E ) => intersectResult ( E ) </k>
endmodule
