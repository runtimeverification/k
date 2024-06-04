// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

module TEST-SYNTAX
    syntax Pgm ::= "quux"
endmodule

module TEST
    imports TEST-SYNTAX
    imports INT

    configuration <k> $PGM:Pgm </k>
        <c1> .K </c1>
        <c2> .K </c2>

    rule <k> quux => .K </k>
        <c1> .K => !C:Int </c1>
        <c2> .K => !C:Int </c2>
endmodule
