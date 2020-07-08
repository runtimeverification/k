// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module INKEYS-16-SPEC
    imports MAP-TESTS

    rule <k> inkeys ( X:MyId in_keys ( M:Map [ Z:MyId <- 1 ] [ X      <- 0 ] ) ) => . </k>

endmodule
