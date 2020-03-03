// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIF-SYNTAX
    imports INT

    syntax S ::= "a" | "b"

endmodule

module VERIF
    imports VERIF-SYNTAX

    configuration <k> $PGM:S </k>

    rule a => b

endmodule
