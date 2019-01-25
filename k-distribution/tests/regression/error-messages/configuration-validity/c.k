// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module C-SYNTAX
    syntax Pgm
endmodule

module C
    imports C-SYNTAX

configuration
<T>
    <k> $PGM:Pgm </k>
    <a3>
        <a4>
            <a5> .K </a5>
        </a4>
    </a3>
    <b3>
        <b4>
            <b5> .K </b5>
        </b4>
        <c4> .K </c4>
    </b3>
</T>

rule <unknown> 1 => 2 </unknown>

endmodule
