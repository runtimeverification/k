// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "map-tests.k"

module LOOKUP-3-SPEC
    imports MAP-TESTS

    claim <k> lookup ( (MAP:Map X:MyId |-> 1) [Y:MyId <- 2] [ Z:MyId ] ) => . </k> requires Y ==K X andBool Z =/=K Y andBool Z =/=K X

endmodule
