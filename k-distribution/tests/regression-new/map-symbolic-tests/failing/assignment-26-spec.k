// Copyright (c) 2019 K Team. All Rights Reserved.

requires "../map-tests.k"

module ASSIGNMENT-26-SPEC
    imports MAP-TESTS

    rule <k> assignment ( (X:MyId |-> 3 1 |-> 4) [ 0 <- 5 ] ) => . </k> requires X =/=K 1

endmodule
