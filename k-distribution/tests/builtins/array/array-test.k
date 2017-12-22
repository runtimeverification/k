require "domains.k"

module ARRAY-TEST-SYNTAX
    imports ARRAY
    imports INT

    syntax Output ::= "assert" Bool
    syntax Program ::= Output | Program Program [left]
endmodule

module ARRAY-TEST
    imports ARRAY-TEST-SYNTAX

    configuration <k> $PGM:Program </k>

    rule P1:Program P2:Program => P1 ~> P2
    rule assert true => .K

endmodule
