// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module E-SYNTAX
    syntax Pgm
endmodule

module E
    imports E-SYNTAX

configuration <T>
    <k> $PGM:Pgm </k>
    <in stream="stdin"> "x" </in>
</T>

endmodule
