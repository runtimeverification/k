// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module INKEYS-12-SPEC
    imports MAP-TESTS

    rule <k> inkeys ( X:MyId in_keys ( M:Map [ X      <- 0 ] ) ) => . </k>

endmodule
