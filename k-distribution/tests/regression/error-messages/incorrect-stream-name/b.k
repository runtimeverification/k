// Copyright (c) 2015-2019 K Team. All Rights Reserved.

module B-SYNTAX
    syntax Pgm
endmodule

module B
    imports B-SYNTAX

    configuration <T>
        <k> $PGM:Pgm </k>
        <in stream="stdinn"> .List </in>
    </T>

endmodule
