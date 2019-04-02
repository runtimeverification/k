// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module ASSIGNMENT-27-SPEC
    imports MAP-TESTS

    rule <k> assignment ( (X:MyId |-> 4) [ X <- 3 ] ) => . </k>

endmodule
