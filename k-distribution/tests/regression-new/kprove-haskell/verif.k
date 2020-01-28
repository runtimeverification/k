// Copyright (c) 2019 K Team. All Rights Reserved.

module VERIF-SYNTAX
    imports INT

    syntax Int ::= "foo"
    rule foo => 3 [macro]

    syntax Pgm ::= doIt ( Int )
endmodule

module VERIF
    imports VERIF-SYNTAX

    configuration <k> $PGM:Pgm </k>

    rule <k> doIt(I => I -Int 1) ... </k> requires I >Int 0
endmodule
