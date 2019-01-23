// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module G-SYNTAX
    syntax Pgm
endmodule

module G
    imports G-SYNTAX

configuration
<T>
    <k> $PGM:Pgm </k>
    <a> .K </a>
    <a> .K </a>
</T>

endmodule
