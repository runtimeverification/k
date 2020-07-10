// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module ASSIGNMENT-24-SPEC
    imports MAP-TESTS

    rule <k> assignment ( (MAP:Map X:MyId |-> 1) [ Y:MyId <- 2 ] [ Z:MyId <- 3 ] ) => assignmentResult ( ( MAP  X |-> 1 ) [ Y <- 2 ] [ Z <- 3 ] )   </k> requires Z =/=K Y

endmodule
