// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module C-SYNTAX
    syntax Pgm
endmodule

module C
    imports C-SYNTAX

configuration <T>
    <k> $PGM:Pgm </k>
    <in stream="stdin"> .List </in>
</T>

endmodule
