// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module D-SYNTAX
    syntax Pgm
endmodule

module D
    imports D-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax KItem ::= Int "+" List{Int,""}

endmodule
