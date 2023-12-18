// Copyright (c) Runtime Verification, Inc. All Rights Reserved.

require "test.k"

module EXPLICIT-SPEC
    imports TEST

    claim <k> quux => . </k>
        <c1> . => ?C </c1>
        <c2> . => ?C </c2>
        <generatedCounter> GC => GC +Int 1 </generatedCounter>
endmodule
