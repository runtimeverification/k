// Copyright (c) Runtime Verification, Inc. All Rights Reserved.
// generated by gen-tests.sh

requires "map-tests.k"

module REMOVE-10-SPEC
    imports MAP-TESTS

    claim <k> remove ( (MAP:Map X:MyId |-> 1) [Y:MyId <- undef] [ Z:MyId ] ) => . </k> requires Z  ==K X

endmodule
