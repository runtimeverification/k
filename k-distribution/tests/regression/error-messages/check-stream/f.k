// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module F-SYNTAX
    syntax Pgm
endmodule

module F
    imports F-SYNTAX

configuration <T>
    <k> $PGM:Pgm </k>
    <in stream="stdin"> 0 1 </in>
</T>

endmodule
