// Copyright (c) 2016-2019 K Team. All Rights Reserved.
requires "domains.k"

module NEGMINT-TEST-SYNTAX
    imports MINT

    syntax Task ::=  "negate" "(" Int "," Int ")" [function]
    syntax Tasks ::= List{Task, ""}
endmodule

module NEGMINT-TEST
    imports NEGMINT-TEST-SYNTAX

    configuration <k>$PGM:Tasks</k>

    rule negate(W:Int, I:Int) => negMInt(mi(W, I))
endmodule
