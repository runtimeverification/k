// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module INKEYS-19-SPEC
    imports MAP-TESTS

    rule <k> inkeys ( Y:MyId in_keys ( M:Map [ Z:MyId <- 1 ] [ X:MyId <- 0 ] ) ) => . </k> requires notBool Y in_keys(M)

endmodule
