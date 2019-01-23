// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module G-SYNTAX
    syntax Pgm
endmodule

module G
    imports G-SYNTAX

configuration <T>
    <k> $PGM:Pgm </k>
    <in stream="stdin"> ListItem(0) ListItem(1) </in>
</T>

endmodule
