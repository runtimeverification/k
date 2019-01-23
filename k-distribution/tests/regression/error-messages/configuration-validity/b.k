// Copyright (c) 2016-2019 K Team. All Rights Reserved.

module B-SYNTAX
    syntax Pgm
endmodule

module B
    imports B-SYNTAX

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

rule <a5> 1 => 2 </a5> <a5> 3 </a5>

endmodule
