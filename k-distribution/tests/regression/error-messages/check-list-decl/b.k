// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module B-SYNTAX
    syntax Pgm
endmodule

module B
    imports B-SYNTAX

configuration <T> <k> $PGM:Pgm </k> </T>

syntax KItem ::= List{Int,""}

endmodule
