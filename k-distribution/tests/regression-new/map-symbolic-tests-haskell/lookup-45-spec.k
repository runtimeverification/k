// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "map-tests.k"

module LOOKUP-45-SPEC
    imports MAP-TESTS

    claim <k> lookup ( (X:MyId |-> 1 Y:MyId |-> 2 MAP:Map) [ Y:MyId ] orDefault 0 ) => . </k> requires X =/=K Y

endmodule
