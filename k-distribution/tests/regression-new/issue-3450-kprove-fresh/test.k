// Copyright (c) K Team. All Rights Reserved.

module TEST-SYNTAX
    syntax Pgm ::= "quux"
endmodule

module TEST
    imports TEST-SYNTAX
    imports INT

    configuration <k> $PGM:Pgm </k>
        <c1> . </c1>
        <c2> . </c2>

    rule <k> quux => . </k>
        <c1> . => !C:Int </c1>
        <c2> . => !C:Int </c2>
endmodule
