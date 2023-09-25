// Copyright (c) K Team. All Rights Reserved.

module TEST-SYNTAX
    imports INT-SYNTAX
    imports ID-SYNTAX
    syntax Exp ::= Exp "+" Exp [left] | Int | Id
endmodule

module TEST
    imports TEST-SYNTAX
    configuration <k> $PGM:Exp </k>

endmodule
