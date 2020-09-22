// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module INKEYS-13-SPEC
    imports MAP-TESTS

    rule <k> inkeys ( Y:MyId in_keys ( M:Map [ X:MyId <- 0 ] ) ) => . </k>

endmodule
