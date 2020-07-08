// Copyright (c) 2019 K Team. All Rights Reserved.

requires "map-tests.k"

module LOOKUP-21-SPEC
    imports MAP-TESTS

    rule <k> lookup ( (Y:MyId |-> 1 X:MyId |-> 2 MAP:Map) [ Y:MyId ] ) => . </k> requires X =/=K Y

endmodule
