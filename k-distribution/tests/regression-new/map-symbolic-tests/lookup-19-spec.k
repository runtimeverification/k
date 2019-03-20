// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module LOOKUP-19-SPEC
    imports MAP-TESTS

    rule <k> lookup ( (Y:MyId |-> 1 MAP:Map X:MyId |-> 2) [ Y:MyId ] ) => . </k> requires X =/=K Y

endmodule
