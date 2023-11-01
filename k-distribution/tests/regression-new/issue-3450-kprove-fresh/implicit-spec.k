// Copyright (c) K Team. All Rights Reserved.

require "test.k"

module IMPLICIT-SPEC
    imports TEST

    claim <k> quux => . </k>
        <c1> . => ?C </c1>
        <c2> . => ?C </c2>
endmodule
