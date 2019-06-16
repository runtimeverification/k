// Copyright (c) 2019 K Team. All Rights Reserved.

module LIST-IN-SYNTAX
    imports INT
    syntax Pgm ::= init ( Int )
endmodule

module LIST-IN
    imports LIST-IN-SYNTAX

    configuration <k> $PGM:Pgm </k>

    rule <k> init(0) => 3 in ListItem ( 3 ) ... </k>
endmodule
