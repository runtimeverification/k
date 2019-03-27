// Copyright (c) 2014-2019 K Team. All Rights Reserved.

module MAP-TESTS-SYNTAX
    imports MAP
    imports INT

    syntax MyId ::= "x" | "y" | "z" | foo ( MyId )

    syntax Test ::= Int | Map
                  | lookup       ( K ) | assignment       ( Map ) | inkeys       ( Bool )
                  | lookupResult ( K ) | assignmentResult ( Map ) | inkeysResult ( Bool )
endmodule

module MAP-TESTS
    imports MAP-TESTS-SYNTAX
    imports MAP-SYMBOLIC

    configuration <k> $PGM:Test </k>

    rule <k> lookup     ( K ) => lookupResult     ( K ) </k>
    rule <k> assignment ( M ) => assignmentResult ( M ) </k>
    rule <k> inkeys     ( M ) => inkeysResult     ( M ) </k>
endmodule
