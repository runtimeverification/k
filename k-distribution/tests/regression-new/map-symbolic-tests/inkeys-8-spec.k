// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module INKEYS-8-SPEC
    imports MAP-TESTS

    rule <k> inkeys ( X:MyId in_keys ( Z:MyId |-> 1 M:Map X      |-> 0 ) ) => . </k>

endmodule
