// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module ASSIGNMENT-13-SPEC
    imports MAP-TESTS

    rule <k> assignment ( (MAP:Map X:MyId |-> 1) [ Y:MyId <- 2 ] [ Z:MyId <- 3 ] ) => assignmentResult (   MAP [ Y <- 2 ]  X |-> 3              )   </k> requires Y =/=K X andBool Z =/=K Y andBool Z  ==K X

endmodule
