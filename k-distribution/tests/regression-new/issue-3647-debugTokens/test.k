// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module TEST-SYNTAX
    imports INT-SYNTAX
    imports ID-SYNTAX
    imports STRING-SYNTAX
    syntax Exp ::= Exp "+" Exp [left] | Int | Id | String
endmodule

module TEST
    imports TEST-SYNTAX
    configuration <k> $PGM:Exp </k>

endmodule
