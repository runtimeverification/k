// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module LOOKUP-18-SPEC
    imports MAP-TESTS

    rule <k> lookup ( (X:MyId |-> 1 MAP:Map Y:MyId |-> 2) [ Y:MyId ] ) => . </k> requires X =/=K Y

endmodule
