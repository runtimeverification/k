// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module LOOKUP-20-SPEC
    imports MAP-TESTS

    rule <k> lookup ( (X:MyId |-> 1 Y:MyId |-> 2 MAP:Map) [ Y:MyId ] ) => . </k> requires X =/=K Y

endmodule
