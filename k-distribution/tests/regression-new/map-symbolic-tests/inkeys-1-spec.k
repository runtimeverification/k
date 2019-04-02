// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module INKEYS-1-SPEC
    imports MAP-TESTS

    rule <k> inkeys ( X:MyId in_keys ( .Map  ) ) => . </k>

endmodule
