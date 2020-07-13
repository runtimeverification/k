// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module ASSIGNMENT-4-SPEC
    imports MAP-TESTS

    rule <k> assignment ( (MAP:Map X:MyId |-> 1) [ Y:MyId <- 2 ] [ Z:MyId <- 3 ] ) => . </k> requires Y =/=K X andBool Y in_keys(MAP)

endmodule
