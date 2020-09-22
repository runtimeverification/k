// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module INKEYS-14-SPEC
    imports MAP-TESTS

    rule <k> inkeys ( Y:MyId in_keys ( M:Map [ X:MyId <- 0 ] ) ) => . </k> requires Y in_keys(M)

endmodule
