// Copyright (c) 2019 K Team. All Rights Reserved.

module ITE-BUG-SYNTAX
    imports INT
    imports K-EQUAL

    syntax Pgm ::= "init"
endmodule

module ITE-BUG
    imports ITE-BUG-SYNTAX

    configuration <k> $PGM:Pgm </k>

    rule <k> init => #if 3 <Int 4 #then 1 #else -1 #fi </k>
endmodule
