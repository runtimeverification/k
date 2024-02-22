// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

requires "test.k"

module EXPLICIT-SPEC
    imports TEST

    claim <k> quux => .K </k>
        <c1> .K => ?C </c1>
        <c2> .K => ?C </c2>
        <generatedCounter> GC => GC +Int 1 </generatedCounter>
endmodule
