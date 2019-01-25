// Copyright (c) 2015-2019 K Team. All Rights Reserved.

module B-SYNTAX
    syntax Pgm ::= "run"
endmodule

module B
    imports B-SYNTAX

    configuration <T>
        <k> $PGM:Pgm </k>
        <a> $XA:Int </a>
        <b> $XB:Int </b>
    </T>

    rule run => 0

endmodule
